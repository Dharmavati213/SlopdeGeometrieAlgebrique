/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import SGA.Foundations.QuasiCoherent.SpecSections
import SGA.Foundations.Differentials.AffineOpens
import SGA.Foundations.Differentials.Exact
import SGA.Foundations.Differentials.QuasiCoherent
import SGA.SGA1.ExposeII.Differentials
import SGA.SGA1.ExposeII.SchemeDifferentials

/-!
# SGA 1, Exposé II, II.4.3 (i), II.4.4 and II.4.6 for sheaves of differentials

For morphisms `f : X ⟶ Y` and `g : Y ⟶ S`, the canonical map `f^* Ω_{Y/S} ⟶ Ω_{X/S}`
(`Scheme.Hom.pullbackRelativeDifferentialsMap`) is computed on affine opens: for affine opens
`W ⊆ S`, `V ⊆ g⁻¹ W`, `U ⊆ f⁻¹ V` with rings `A`, `B`, `C`, there is a `C`-linear isomorphism
`Γ(U, f^* Ω_{Y/S}) ≅ C ⊗_B Ω_{B/A}` under which the map on sections over `U` is
`C ⊗_B Ω_{B/A} → Ω_{C/A}` (`exists_linearEquiv_pullbackRelativeDifferentialsMap_app`). The
sections of the inverse image of a quasi-coherent module over such a `U` are computed in
`pullbackSectionsAddEquiv` (Stacks 01I9), from `pullbackSpecMapΓAddEquiv` of `SGA.Foundations`.

With the ring-level statements of `SGA.SGA1.ExposeII.Differentials` this gives:

* II.4.3 (i): for `f` smooth, `0 → f^* Ω_{Y/S} → Ω_{X/S} → Ω_{X/Y} → 0` is exact
  (`shortExact_relativeDifferentialsShortComplex_of_smooth`); locally, `f^* Ω_{Y/S} → Ω_{X/S}` is
  injective on the sections over every open of the smooth locus of `f`
  (`injective_app_pullbackRelativeDifferentialsMap_of_le_smoothLocus`);
* II.4.4: the map is a monomorphism with locally free cokernel `Ω_{X/Y}`
  (`mono_pullbackRelativeDifferentialsMap_and_isLocallyFree_of_smooth`), and on affine opens the
  map on sections has a linear retraction
  (`exists_retraction_app_pullbackRelativeDifferentialsMap`);
* II.4.6: a morphism of smooth `S`-schemes (locally of finite presentation) is étale iff
  `f^* Ω_{Y/S} ⟶ Ω_{X/S}` is an isomorphism (`etale_iff_isIso_pullbackRelativeDifferentialsMap`),
  and, on affine opens, `Γ(Y, V) → Γ(X, U)` is étale iff the map on sections over `U` is bijective
  (`bijective_app_pullbackRelativeDifferentialsMap_iff`).

II.4.6 is stated globally and on the affine opens of a basis; the pointwise form "at `x`" is the
statement for the local rings, `SGA.SGA1.ExposeII.etale_iff_mapBaseChange_bijective`.
-/

universe u

open CategoryTheory Opposite TensorProduct AlgebraicGeometry Scheme.Modules

namespace SGA.SGA1.ExposeII

section PullbackSections

variable {X Y : Scheme.{u}}

/-- Along an open immersion whose image contains `W`, the inverse image of sections over `W` is
bijective onto the global sections. -/
lemma pullbackAppTop_bijective_of_isOpenImmersion (h : X ⟶ Y) [IsOpenImmersion h]
    (M : Y.Modules) (W : Y.Opens) (hW : W ≤ h.opensRange) (ht : ⊤ ≤ h ⁻¹ᵁ W) :
    Function.Bijective (pullbackAppTop h M W ht) := by
  have e : ⇑(pullbackAppTop h M W ht) =
      ⇑(((pullback h).obj M).presheaf.map (homOfLE ht).op) ∘ ⇑(pullbackApp h M W) := by
    ext x
    simp only [pullbackAppTop]
    erw [ConcreteCategory.comp_apply]
    rfl
  rw [e]
  exact (TopCat.Presheaf.map_bijective_of_eq _ _ (top_le_iff.mp ht).symm).comp
    (pullbackApp_bijective_of_isOpenImmersion h M W hW)

/-- `pullbackAppTop` commutes with restriction of sections. -/
lemma pullbackAppTop_map (w : X ⟶ Y) (P : Y.Modules) {W W' : Y.Opens} (i : W ≤ W')
    (h : ⊤ ≤ w ⁻¹ᵁ W) (h' : ⊤ ≤ w ⁻¹ᵁ W') (z : Γ(P, W')) :
    pullbackAppTop w P W h (P.presheaf.map (homOfLE i).op z) = pullbackAppTop w P W' h' z := by
  simp only [pullbackAppTop]
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  rw [pullbackApp_map]
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

variable {U : X.Opens} (hU : IsAffineOpen U)

/-- Inverse images of sections along `Spec Γ(X, U) ⟶ X` are `Γ(X, U)`-linear. -/
lemma pullbackAppTop_fromSpec_smul (P : X.Modules) (h : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) (r : Γ(X, U))
    (s : Γ(P, U)) :
    pullbackAppTop hU.fromSpec P U h (r • s) = r • pullbackAppTop hU.fromSpec P U h s := by
  simp only [pullbackAppTop]
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  rw [pullbackApp_smul, Scheme.Modules.map_smul, smul_Spec_def]
  congr 1
  rw [hU.fromSpec_app_self]
  erw [ConcreteCategory.comp_apply]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  have h₁ : (⊤ : (Spec Γ(X, U)).Opens).leTop = 𝟙 _ := Subsingleton.elim _ _
  rw [h₁, op_id, CategoryTheory.Functor.map_id]
  rw [show (eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE h).op = 𝟙 _ from
    Quiver.Hom.unop_inj (Subsingleton.elim _ _), CategoryTheory.Functor.map_id]

section Chart

variable (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent] {U : X.Opens} {V : Y.Opens}
  (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V)

/-- For affine opens `U ⊆ f⁻¹ V`, `(f^* M)|_U` and the inverse image of `M|_V` along
`Spec Γ(X, U) ⟶ Spec Γ(Y, V)` agree on `Spec Γ(X, U)`. -/
noncomputable def chartIso : (pullback hU.fromSpec).obj ((pullback f).obj M) ≅
    (pullback (Spec.map (f.appLE V U e))).obj ((pullback hV.fromSpec).obj M) :=
  (pullbackCompIso' hU.fromSpec f _ rfl M).symm ≪≫
    pullbackCompIso' (Spec.map (f.appLE V U e)) hV.fromSpec _
      (IsAffineOpen.SpecMap_appLE_fromSpec f hV hU e) M

/-- The sections of `f^* M` over an affine open `U ⊆ f⁻¹ V`, `V` affine, are
`Γ(X, U) ⊗_{Γ(Y, V)} Γ(V, M)` (Stacks 01I9); here `Γ(V, M)` appears as the global sections of the
restriction of `M` to `Spec Γ(Y, V)`. -/
noncomputable def pullbackSectionsAddEquiv :
    Γ((pullback f).obj M, U) ≃+
      (ModuleCat.extendScalars (f.appLE V U e).hom).obj ((pullback hV.fromSpec).obj M).ΓSpec :=
  (AddEquiv.ofBijective
      (pullbackAppTop hU.fromSpec ((pullback f).obj M) U hU.fromSpec_preimage_self.ge).hom
      (pullbackAppTop_bijective_of_isOpenImmersion _ _ _ hU.opensRange_fromSpec.ge _)).trans
    ((isoAppAddEquiv (chartIso f M hU hV e) ⊤).trans
      (pullbackSpecMapΓAddEquiv (f.appLE V U e) ((pullback hV.fromSpec).obj M)))

/-- `pullbackSectionsAddEquiv` sends `c · f^* m` to `c ⊗ m`. -/
lemma pullbackSectionsAddEquiv_smul_pullbackApp (c : Γ(X, U)) (m : Γ(M, V)) :
    pullbackSectionsAddEquiv f M hU hV e
        (c • ((pullback f).obj M).presheaf.map (homOfLE e).op (pullbackApp f M V m)) =
      c • oneTmul _ (f.appLE V U e)
        (pullbackAppTop hV.fromSpec M V hV.fromSpec_preimage_self.ge m) := by
  have hq : ⊤ ≤ (hU.fromSpec ≫ f) ⁻¹ᵁ V := by
    rw [Scheme.Hom.comp_preimage]
    exact hU.fromSpec_preimage_self.ge.trans (Scheme.Hom.preimage_mono _ e)
  have h' : ⊤ ≤ hU.fromSpec ⁻¹ᵁ (f ⁻¹ᵁ V) := hq
  have hf : ⊤ ≤ Spec.map (f.appLE V U e) ⁻¹ᵁ (hV.fromSpec ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, IsAffineOpen.SpecMap_appLE_fromSpec f hV hU e]
    exact hq
  simp only [pullbackSectionsAddEquiv, AddEquiv.trans_apply, AddEquiv.ofBijective_apply]
  erw [pullbackAppTop_fromSpec_smul hU _ hU.fromSpec_preimage_self.ge c]
  rw [pullbackAppTop_map hU.fromSpec _ e _ h']
  change pullbackSpecMapΓAddEquiv _ _ ((chartIso f M hU hV e).hom.app ⊤
    (c • pullbackAppTop hU.fromSpec _ (f ⁻¹ᵁ V) h' (pullbackApp f M V m))) = _
  rw [Hom.app_smul_Spec, chartIso, Iso.trans_hom, Hom.comp_app_apply, Iso.symm_hom,
    pullbackCompIso'_inv_app_pullbackAppTop hU.fromSpec f _ rfl M V hq h' m,
    pullbackCompIso'_hom_app_pullbackAppTop _ _ _ (IsAffineOpen.SpecMap_appLE_fromSpec f hV hU e)
      M V hq hf m,
    ← pullbackAppTop_map _ _ hV.fromSpec_preimage_self.ge (top_le_preimage_top _) hf]
  change pullbackSpecMapΓAddEquiv _ _ (c • pullbackAppTop _ _ ⊤ (top_le_preimage_top _)
    (pullbackAppTop hV.fromSpec M V hV.fromSpec_preimage_self.ge m)) = _
  rw [← pullbackSpecMapΓAddEquiv_symm_smul_oneTmul, AddEquiv.apply_symm_apply]

/-- `pullbackSectionsAddEquiv` is `Γ(X, U)`-linear. -/
lemma pullbackSectionsAddEquiv_smul (c : Γ(X, U)) (t : Γ((pullback f).obj M, U)) :
    pullbackSectionsAddEquiv f M hU hV e (c • t) = c • pullbackSectionsAddEquiv f M hU hV e t := by
  simp only [pullbackSectionsAddEquiv, AddEquiv.trans_apply, AddEquiv.ofBijective_apply]
  erw [pullbackAppTop_fromSpec_smul hU _ hU.fromSpec_preimage_self.ge c]
  change pullbackSpecMapΓAddEquiv _ _ ((chartIso f M hU hV e).hom.app ⊤ (c • _)) = _
  rw [Hom.app_smul_Spec, pullbackSpecMapΓAddEquiv_smul]
  rfl

end Chart

end PullbackSections

section Differentials

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- `f^* Ω_{Y/S} ⟶ Ω_{X/S}` on inverse images of sections: `f^* ω ↦ f^♯ ω`. -/
lemma pullbackRelativeDifferentialsMap_app_pullbackApp (V : Y.Opens)
    (m : Γ(g.relativeDifferentials, V)) :
    (f.pullbackRelativeDifferentialsMap g).app (f ⁻¹ᵁ V)
        (pullbackApp f g.relativeDifferentials V m) =
      (f.relativeDifferentialsToPushforward g).app V m := by
  have h := (pullbackPushforwardAdjunction f).homEquiv_unit (X := g.relativeDifferentials)
    (Y := (f ≫ g).relativeDifferentials) (f.pullbackRelativeDifferentialsMap g)
  rw [Scheme.Hom.pullbackRelativeDifferentialsMap, Equiv.apply_symm_apply] at h
  rw [h]
  rfl

variable {U : X.Opens} {V : Y.Opens} {W : S.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
  (hW : IsAffineOpen W) (eU : U ≤ f ⁻¹ᵁ V) (eV : V ≤ g ⁻¹ᵁ W)

include eU eV in
/-- `U ⊆ f⁻¹ V` and `V ⊆ g⁻¹ W` give `U ⊆ (f ≫ g)⁻¹ W`. -/
lemma le_preimage_comp : U ≤ (f ≫ g) ⁻¹ᵁ W := by
  rw [Scheme.Hom.comp_preimage]
  exact eU.trans (Scheme.Hom.preimage_mono f eV)

/-- The inverse image of sections along `Spec Γ(Y, V) ⟶ Y`, as a `Γ(Y, V)`-linear equivalence. -/
noncomputable def pullbackAppTopFromSpecEquiv (P : Y.Modules) :
    Γ(P, V) ≃ₗ[Γ(Y, V)] ((pullback hV.fromSpec).obj P).ΓSpec :=
  LinearEquiv.ofBijective
    { toFun := pullbackAppTop hV.fromSpec P V hV.fromSpec_preimage_self.ge
      map_add' := map_add _
      map_smul' := pullbackAppTop_fromSpec_smul hV P _ }
    (pullbackAppTop_bijective_of_isOpenImmersion _ _ _ hV.opensRange_fromSpec.ge _)

/-- `Γ(S, W) → Γ(Y, V) → Γ(X, U)` is `Γ(S, W) → Γ(X, U)`. -/
lemma appLE_comp_appLE_eq :
    g.appLE W V eV ≫ f.appLE V U eU = (f ≫ g).appLE W U (le_preimage_comp f g eU eV) :=
  Scheme.Hom.appLE_comp_appLE f g W V U eV eU

include hV in
open KaehlerDifferential in
/-- **Sections of `f^* Ω_{Y/S} ⟶ Ω_{X/S}` on affine opens**: for affine opens `W ⊆ S`,
`V ⊆ g⁻¹ W`, `U ⊆ f⁻¹ V` with rings `A`, `B`, `C`, the map on sections over `U` is
`C ⊗_B Ω_{B/A} → Ω_{C/A}`, `c ⊗ db ↦ c d(b)`, under `Γ(U, f^* Ω_{Y/S}) ≅ C ⊗_B Ω_{B/A}` and
`Γ(U, Ω_{X/S}) ≅ Ω_{C/A}`. -/
theorem exists_linearEquiv_pullbackRelativeDifferentialsMap_app :
    letI := (g.appLE W V eV).hom.toAlgebra
    letI := (f.appLE V U eU).hom.toAlgebra
    letI := ((f ≫ g).appLE W U (le_preimage_comp f g eU eV)).hom.toAlgebra
    ∃ (_ : IsScalarTower Γ(S, W) Γ(Y, V) Γ(X, U))
      (E : Γ((pullback f).obj g.relativeDifferentials, U) ≃ₗ[Γ(X, U)]
        Γ(X, U) ⊗[Γ(Y, V)] Ω[Γ(Y, V)⁄Γ(S, W)]),
      ∀ t, (f ≫ g).relativeDifferentialsAppEquiv hU hW (le_preimage_comp f g eU eV)
          ((f.pullbackRelativeDifferentialsMap g).app U t) =
        mapBaseChange Γ(S, W) Γ(Y, V) Γ(X, U) (E t) := by
  let := (g.appLE W V eV).hom.toAlgebra
  let := (f.appLE V U eU).hom.toAlgebra
  let := ((f ≫ g).appLE W U (le_preimage_comp f g eU eV)).hom.toAlgebra
  have hST : IsScalarTower Γ(S, W) Γ(Y, V) Γ(X, U) := IsScalarTower.of_algebraMap_eq' (by
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
      ← appLE_comp_appLE_eq f g eU eV, CommRingCat.hom_comp])
  refine ⟨hST, ?_⟩
  let eV' : Γ(g.relativeDifferentials, V) ≃ₗ[Γ(Y, V)] Ω[Γ(Y, V)⁄Γ(S, W)] :=
    g.relativeDifferentialsAppEquiv hV hW eV
  have heV (b : Γ(Y, V)) : eV' (g.universalDerivation.app V b) = D _ _ b :=
    g.relativeDifferentialsAppEquiv_universalDerivation hV hW eV b
  let eU' : Γ((f ≫ g).relativeDifferentials, U) ≃ₗ[Γ(X, U)] Ω[Γ(X, U)⁄Γ(S, W)] :=
    (f ≫ g).relativeDifferentialsAppEquiv hU hW (le_preimage_comp f g eU eV)
  have heU (c : Γ(X, U)) : eU' ((f ≫ g).universalDerivation.app U c) = D _ _ c :=
    (f ≫ g).relativeDifferentialsAppEquiv_universalDerivation hU hW _ c
  set F4 := pullbackAppTopFromSpecEquiv hV g.relativeDifferentials
  let G : ((pullback hV.fromSpec).obj g.relativeDifferentials).ΓSpec ≃ₗ[Γ(Y, V)]
      Ω[Γ(Y, V)⁄Γ(S, W)] := F4.symm.trans eV'
  let E₀ := pullbackSectionsAddEquiv f g.relativeDifferentials hU hV eU
  let Θ : Γ(X, U) ⊗[Γ(Y, V)] ((pullback hV.fromSpec).obj g.relativeDifferentials).ΓSpec ≃+
      Γ(X, U) ⊗[Γ(Y, V)] Ω[Γ(Y, V)⁄Γ(S, W)] := (LinearEquiv.lTensor Γ(X, U) G).toAddEquiv
  have hΘ (c : Γ(X, U))
      (y : Γ(X, U) ⊗[Γ(Y, V)] ((pullback hV.fromSpec).obj g.relativeDifferentials).ΓSpec) :
      Θ (c • y) = c • Θ y := by
    induction y using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul c' n => simp [Θ, TensorProduct.smul_tmul']
    | add y z hy hz => simp only [smul_add, map_add, hy, hz]
  let E : Γ((pullback f).obj g.relativeDifferentials, U) ≃ₗ[Γ(X, U)]
      Γ(X, U) ⊗[Γ(Y, V)] Ω[Γ(Y, V)⁄Γ(S, W)] :=
    { E₀.trans Θ with
      map_smul' c t := by
        change Θ (E₀ (c • t)) = c • Θ (E₀ t)
        rw [show E₀ (c • t) = c • E₀ t from
          pullbackSectionsAddEquiv_smul f g.relativeDifferentials hU hV eU c t]
        exact hΘ c (E₀ t) }
  refine ⟨E, ?_⟩
  have hstar : ∀ m : Γ(g.relativeDifferentials, V),
      eU' ((f ≫ g).relativeDifferentials.presheaf.map (homOfLE eU).op
        ((f.relativeDifferentialsToPushforward g).app V m)) =
      map Γ(S, W) Γ(S, W) Γ(Y, V) Γ(X, U) (eV' m) := by
    intro m
    obtain ⟨ω, rfl⟩ := eV'.symm.surjective m
    rw [LinearEquiv.apply_symm_apply]
    have hω : ω ∈ Submodule.span Γ(Y, V) (Set.range (D Γ(S, W) Γ(Y, V))) := by
      rw [span_range_derivation]; trivial
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      have hb : eV'.symm (D _ _ b) = g.universalDerivation.app V b := by
        rw [LinearEquiv.symm_apply_eq, heV]
      rw [hb, Scheme.Hom.relativeDifferentialsToPushforward_app]
      erw [← Scheme.Modules.Derivation.app_map]
      erw [heU]
      rw [map_D]
      rfl
    | zero =>
      simp only [map_zero]
      erw [map_zero, map_zero]
    | add x y _ _ hx hy =>
      simp only [map_add]
      erw [map_add]
      rw [map_add, hx, hy]
    | smul b x _ hx =>
      rw [map_smul eV'.symm, Hom.app_smul]
      erw [Scheme.Modules.map_smul]
      rw [map_smul eU', hx, LinearMap.map_smul, ← algebraMap_smul Γ(X, U) b]
      rfl
  intro t
  obtain ⟨y, rfl⟩ := E₀.symm.surjective t
  change eU' ((f.pullbackRelativeDifferentialsMap g).app U (E₀.symm y)) =
    mapBaseChange Γ(S, W) Γ(Y, V) Γ(X, U) (Θ (E₀ (E₀.symm y)))
  rw [AddEquiv.apply_symm_apply]
  induction y using TensorProduct.induction_on with
  | zero =>
    have h0 : E₀.symm 0 = 0 := E₀.symm.map_zero
    have h1 : Θ 0 = 0 := Θ.map_zero
    erw [h0, h1]
    simp only [map_zero]
  | add y z hy hz =>
    have h0 : E₀.symm (y + z) = E₀.symm y + E₀.symm z := E₀.symm.map_add y z
    have h1 : Θ (y + z) = Θ y + Θ z := Θ.map_add y z
    erw [h0, h1]
    simp only [map_add, hy, hz]
  | tmul c n =>
    obtain ⟨m, rfl⟩ := F4.surjective n
    have hkey := pullbackSectionsAddEquiv_smul_pullbackApp f g.relativeDifferentials hU hV eU c m
    let c' : Γ(X, U) := c
    have h1 : E₀.symm (c ⊗ₜ F4 m) = c' • ((pullback f).obj g.relativeDifferentials).presheaf.map
        (homOfLE eU).op (pullbackApp f g.relativeDifferentials V m) := by
      refine E₀.symm_apply_eq.mpr ?_
      erw [hkey]
      have e : (c' • ((1 : Γ(X, U)) ⊗ₜ[Γ(Y, V)] (F4 m)) :
          Γ(X, U) ⊗[Γ(Y, V)] ((pullback hV.fromSpec).obj g.relativeDifferentials).ΓSpec) =
          c' ⊗ₜ F4 m := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      exact e.symm
    have h2 : Θ (c ⊗ₜ F4 m) = c' ⊗ₜ eV' m := by
      change c ⊗ₜ G (F4 m) = _
      simp [G]
      rfl
    erw [h1, h2]
    rw [Hom.app_smul, _root_.map_smul, Hom.app_map,
      pullbackRelativeDifferentialsMap_app_pullbackApp,
      hstar, mapBaseChange_tmul]

include hU hV hW eV in
/-- II.4.3 (i), on sections over an affine open `U ⊆ f⁻¹ V`: if `Γ(Y, V) → Γ(X, U)` is formally
smooth, then `Γ(U, f^* Ω_{Y/S}) → Γ(U, Ω_{X/S})` is injective. -/
theorem injective_app_pullbackRelativeDifferentialsMap
    (h : (f.appLE V U eU).hom.FormallySmooth) :
    Function.Injective ((f.pullbackRelativeDifferentialsMap g).app U) := by
  let := (g.appLE W V eV).hom.toAlgebra
  let := (f.appLE V U eU).hom.toAlgebra
  let := ((f ≫ g).appLE W U (le_preimage_comp f g eU eV)).hom.toAlgebra
  obtain ⟨_, E, hE⟩ := exists_linearEquiv_pullbackRelativeDifferentialsMap_app f g hU hV hW eU eV
  have : Algebra.FormallySmooth Γ(Y, V) Γ(X, U) := h
  have hκ := mapBaseChange_injective Γ(S, W) Γ(Y, V) Γ(X, U)
  intro t t' htt
  apply E.injective
  apply hκ
  rw [← hE, ← hE, htt]

include hU hV hW in
/-- II.4.6, on sections over an affine open `U ⊆ f⁻¹ V`: if `Γ(Y, V)` and `Γ(X, U)` are smooth
over `Γ(S, W)`, then `Γ(Y, V) → Γ(X, U)` is étale iff `Γ(U, f^* Ω_{Y/S}) → Γ(U, Ω_{X/S})` is
bijective. -/
theorem bijective_app_pullbackRelativeDifferentialsMap_iff
    (hg : (g.appLE W V eV).hom.Smooth)
    (hfg : ((f ≫ g).appLE W U (le_preimage_comp f g eU eV)).hom.Smooth) :
    Function.Bijective ((f.pullbackRelativeDifferentialsMap g).app U) ↔
      (f.appLE V U eU).hom.Etale := by
  let := (g.appLE W V eV).hom.toAlgebra
  let := (f.appLE V U eU).hom.toAlgebra
  let := ((f ≫ g).appLE W U (le_preimage_comp f g eU eV)).hom.toAlgebra
  obtain ⟨_, E, hE⟩ := exists_linearEquiv_pullbackRelativeDifferentialsMap_app f g hU hV hW eU eV
  have : Algebra.Smooth Γ(S, W) Γ(Y, V) := hg
  have : Algebra.Smooth Γ(S, W) Γ(X, U) := hfg
  change _ ↔ Algebra.Etale Γ(Y, V) Γ(X, U)
  rw [etale_iff_mapBaseChange_bijective Γ(S, W) Γ(Y, V) Γ(X, U)]
  set eU' := (f ≫ g).relativeDifferentialsAppEquiv hU hW (le_preimage_comp f g eU eV)
  have hc : ⇑(KaehlerDifferential.mapBaseChange Γ(S, W) Γ(Y, V) Γ(X, U)) =
      ⇑eU' ∘ ⇑((f.pullbackRelativeDifferentialsMap g).app U) ∘ ⇑E.symm := by
    funext y
    simp only [Function.comp_apply]
    rw [hE, LinearEquiv.apply_symm_apply]
  rw [hc]
  constructor
  · intro h
    exact eU'.bijective.comp (h.comp E.symm.bijective)
  · intro h
    have h' : Function.Bijective (⇑eU'.symm ∘
        (⇑eU' ∘ ⇑((f.pullbackRelativeDifferentialsMap g).app U) ∘
        ⇑E.symm) ∘ ⇑E) := eU'.symm.bijective.comp (h.comp E.bijective)
    convert h' using 1
    funext t
    simp

include hU hV hW eV in
/-- II.4.4, on sections over an affine open `U ⊆ f⁻¹ V`: if `Γ(Y, V) → Γ(X, U)` is formally
smooth, then `Γ(U, f^* Ω_{Y/S}) → Γ(U, Ω_{X/S})` has a `Γ(X, U)`-linear retraction, i.e. it is
the inclusion of a direct factor. -/
theorem exists_retraction_app_pullbackRelativeDifferentialsMap
    (h : (f.appLE V U eU).hom.FormallySmooth) :
    ∃ r : Γ((f ≫ g).relativeDifferentials, U) →ₗ[Γ(X, U)]
        Γ((pullback f).obj g.relativeDifferentials, U),
      ∀ t, r ((f.pullbackRelativeDifferentialsMap g).app U t) = t := by
  let := (g.appLE W V eV).hom.toAlgebra
  let := (f.appLE V U eU).hom.toAlgebra
  let := ((f ≫ g).appLE W U (le_preimage_comp f g eU eV)).hom.toAlgebra
  obtain ⟨_, E, hE⟩ := exists_linearEquiv_pullbackRelativeDifferentialsMap_app f g hU hV hW eU eV
  have : Algebra.FormallySmooth Γ(Y, V) Γ(X, U) := h
  obtain ⟨l, hl⟩ := exists_retraction_mapBaseChange Γ(S, W) Γ(Y, V) Γ(X, U)
  let eU' : Γ((f ≫ g).relativeDifferentials, U) ≃ₗ[Γ(X, U)] Ω[Γ(X, U)⁄Γ(S, W)] :=
    (f ≫ g).relativeDifferentialsAppEquiv hU hW (le_preimage_comp f g eU eV)
  refine ⟨E.symm.toLinearMap ∘ₗ l ∘ₗ eU'.toLinearMap, fun t ↦ ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  change E.symm (l (eU' _)) = t
  have hE' : eU' ((f.pullbackRelativeDifferentialsMap g).app U t) =
      KaehlerDifferential.mapBaseChange Γ(S, W) Γ(Y, V) Γ(X, U) (E t) := hE t
  rw [hE', ← LinearMap.comp_apply l, hl, LinearMap.id_apply, LinearEquiv.symm_apply_apply]

end Differentials

section Global

variable {X : Scheme.{u}}

/-- A morphism of `𝒪_X`-modules which is injective on all sections is a monomorphism. -/
lemma mono_of_forall_injective_app {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ U, Function.Injective (φ.app U)) : Mono φ := by
  apply (toPresheaf X).mono_of_mono_map
  have (U : X.Opensᵒᵖ) : Mono (φ.mapPresheaf.app U) :=
    ConcreteCategory.mono_of_injective _ (h U.unop)
  exact NatTrans.mono_of_mono_app φ.mapPresheaf

/-- A morphism of `𝒪_X`-modules which is injective on the sections over the members of a basis
is injective on all sections. -/
lemma injective_app_of_isBasis {M N : X.Modules} (φ : M ⟶ N) {B : Set X.Opens}
    (hB : TopologicalSpace.Opens.IsBasis B) (h : ∀ U ∈ B, Function.Injective (φ.app U))
    (U : X.Opens) : Function.Injective (φ.app U) :=
  TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective (F := ⟨M.presheaf, M.isSheaf⟩)
    φ.mapPresheaf U fun x _ ↦
      TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis hB (fun U hU ↦ h U hU) x

/-- A morphism of `𝒪_X`-modules which is bijective on the sections over the members of a basis
is an isomorphism. -/
lemma isIso_of_isBasis {M N : X.Modules} (φ : M ⟶ N) {B : Set X.Opens}
    (hB : TopologicalSpace.Opens.IsBasis B) (h : ∀ U ∈ B, Function.Bijective (φ.app U)) :
    IsIso φ := by
  let ψ : (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X) ⟶ ⟨N.presheaf, N.isSheaf⟩ :=
    ObjectProperty.homMk φ.mapPresheaf
  have hB' : TopologicalSpace.Opens.IsBasis (Set.range (Subtype.val : B → X.Opens)) := by
    rwa [Subtype.range_coe]
  have : IsIso ψ := TopCat.Sheaf.isIso_iff_isIso_basis hB' fun i ↦
    (ConcreteCategory.isIso_iff_bijective _).mpr (h i.1 i.2)
  have : IsIso ((toPresheaf X).map φ) :=
    inferInstanceAs (IsIso ((ObjectProperty.ι _).map ψ))
  exact isIso_of_reflects_iso φ (toPresheaf X)

end Global

section Main

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- The affine opens `U ⊆ X` with `U ⊆ f⁻¹ V` and `V ⊆ g⁻¹ W` for some affine opens `V ⊆ Y`,
`W ⊆ S`. -/
def affineChartOpens : Set X.Opens :=
  {U | IsAffineOpen U ∧ ∃ (V : Y.Opens) (W : S.Opens), IsAffineOpen V ∧ IsAffineOpen W ∧
    U ≤ f ⁻¹ᵁ V ∧ V ≤ g ⁻¹ᵁ W}

/-- The opens of `affineChartOpens f g` form a basis of `X`. -/
lemma isBasis_affineChartOpens : TopologicalSpace.Opens.IsBasis (affineChartOpens f g) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g (f x))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (a := f x) hxW (g ⁻¹ᵁ W).2
  obtain ⟨_, ⟨U', hU', rfl⟩, hxU', hU'U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (a := x)
      (show x ∈ ((U ⊓ f ⁻¹ᵁ V : X.Opens) : Set X) from ⟨hx, hxV⟩) (U ⊓ f ⁻¹ᵁ V).2
  exact ⟨U', ⟨hU', V, W, hV, hW, fun y hy ↦ (hU'U hy).2, hVW⟩, hxU', fun y hy ↦ (hU'U hy).1⟩

/-- **II.4.3 (i)**: if `f : X ⟶ Y` is smooth, then `f^* Ω_{Y/S} ⟶ Ω_{X/S}` is a monomorphism. -/
theorem mono_pullbackRelativeDifferentialsMap_of_smooth [Smooth f] :
    Mono (f.pullbackRelativeDifferentialsMap g) := by
  refine mono_of_forall_injective_app _
    (injective_app_of_isBasis _ (isBasis_affineChartOpens f g) ?_)
  rintro U ⟨hU, V, W, hV, hW, eU, eV⟩
  refine injective_app_pullbackRelativeDifferentialsMap f g hU hV hW eU eV ?_
  have := f.smooth_appLE hV hU eU
  algebraize [(f.appLE V U eU).hom]
  exact inferInstanceAs (Algebra.FormallySmooth Γ(Y, V) Γ(X, U))

/-- **II.4.3 (i)**: if `f : X ⟶ Y` is a smooth morphism of `S`-schemes, the sequence
`0 → f^* Ω_{Y/S} → Ω_{X/S} → Ω_{X/Y} → 0` is exact. -/
theorem shortExact_relativeDifferentialsShortComplex_of_smooth [Smooth f] :
    (f.relativeDifferentialsShortComplex g).ShortExact where
  exact := (f.relativeDifferentialsShortComplex_exact g).1
  mono_f := mono_pullbackRelativeDifferentialsMap_of_smooth f g
  epi_g := (f.relativeDifferentialsShortComplex_exact g).2

/-- **II.4.4**: if `f : X ⟶ Y` is smooth, `f^* Ω_{Y/S} ⟶ Ω_{X/S}` is a monomorphism whose cokernel
`Ω_{X/Y}` is locally free; so its image is locally a direct factor (on affine opens this is
`exists_retraction_app_pullbackRelativeDifferentialsMap`). -/
theorem mono_pullbackRelativeDifferentialsMap_and_isLocallyFree_of_smooth [Smooth f] :
    Mono (f.pullbackRelativeDifferentialsMap g) ∧ f.relativeDifferentials.IsLocallyFree :=
  ⟨mono_pullbackRelativeDifferentialsMap_of_smooth f g, inferInstance⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- **II.4.6**: let `f : X ⟶ Y` be a morphism of smooth `S`-schemes, locally of finite
presentation. Then `f` is étale iff `f^* Ω_{Y/S} ⟶ Ω_{X/S}` is an isomorphism. -/
theorem etale_iff_isIso_pullbackRelativeDifferentialsMap [Smooth g] [Smooth (f ≫ g)]
    [LocallyOfFinitePresentation f] :
    Etale f ↔ IsIso (f.pullbackRelativeDifferentialsMap g) := by
  constructor
  · intro hf
    refine isIso_of_isBasis _ (isBasis_affineChartOpens f g) ?_
    rintro U ⟨hU, V, W, hV, hW, eU, eV⟩
    exact (bijective_app_pullbackRelativeDifferentialsMap_iff f g hU hV hW eU eV
      (g.smooth_appLE hW hV eV) ((f ≫ g).smooth_appLE hW hU _)).mpr (f.etale_appLE hV hU eU)
  · intro hiso
    have : FormallyUnramified f :=
      (formallyUnramified_iff_epi_pullbackRelativeDifferentialsMap f g).mpr inferInstance
    have : Smooth f := by
      refine IsZariskiLocalAtSource.iff_exists_resLE.mpr fun x ↦ ?_
      obtain ⟨U, ⟨hU, V, W, hV, hW, eU, eV⟩, hxU, -⟩ :=
        (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_affineChartOpens f g))
          (TopologicalSpace.Opens.mem_top x)
      have H := (bijective_app_pullbackRelativeDifferentialsMap_iff f g hU hV hW eU eV
        (g.smooth_appLE hW hV eV) ((f ≫ g).smooth_appLE hW hU _)).mp
        (ConcreteCategory.bijective_of_isIso _)
      refine ⟨V, U, hxU, eU, ?_⟩
      have : IsAffine V := hV
      have : IsAffine U := hU
      rw [HasRingHomProperty.iff_of_isAffine (P := @Smooth)]
      exact (RingHom.Smooth.propertyIsLocal.respectsIso.arrow_mk_iso_iff
        (arrowResLEAppIso f V U eU)).mpr
        ((RingHom.etale_iff_formallyUnramified_and_smooth _).mp H).2
    exact Etale.of_formallyUnramified_of_flat f

/-- If `U ⊆ f⁻¹ V` are affine opens and `U` lies in the smooth locus of `f`, then
`Γ(Y, V) → Γ(X, U)` is formally smooth. -/
lemma formallySmooth_appLE_of_le_smoothLocus [LocallyOfFinitePresentation f] {U : X.Opens}
    {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V)
    (hW : U ≤ f.smoothLocus) : (f.appLE V U e).hom.FormallySmooth := by
  have := f.finitePresentation_appLE hV hU e
  algebraize [(f.appLE V U e).hom]
  change Algebra.FormallySmooth Γ(Y, V) Γ(X, U)
  rw [← Algebra.smoothLocus_eq_univ_iff]
  refine Set.eq_univ_of_forall fun p ↦ ?_
  have hx : hU.fromSpec p ∈ U := hU.range_fromSpec.le ⟨p, rfl⟩
  have hp : hU.primeIdealOf ⟨hU.fromSpec p, hx⟩ = p :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf ⟨hU.fromSpec p, hx⟩)
  have := (formallySmooth_stalkMap_iff V hV U hU e hx).mp (hW hx)
  rwa [hp] at this

/-- **II.4.3 (i), local form**: on every open `U` contained in the smooth locus of `f`,
`Γ(U, f^* Ω_{Y/S}) → Γ(U, Ω_{X/S})` is injective. -/
theorem injective_app_pullbackRelativeDifferentialsMap_of_le_smoothLocus
    [LocallyOfFinitePresentation f] {U : X.Opens} (hU : U ≤ f.smoothLocus) :
    Function.Injective ((f.pullbackRelativeDifferentialsMap g).app U) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  let ι := {U' : X.Opens // U' ∈ affineChartOpens f g ∧ U' ≤ U}
  refine TopCat.Sheaf.eq_of_locally_eq'
    (⟨_, ((pullback f).obj g.relativeDifferentials).isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun i : ι ↦ i.1) U (fun i ↦ homOfLE i.2.2) (fun x hx ↦ ?_) s 0 fun i ↦ ?_
  · obtain ⟨U', hU', hxU', hU'U⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_affineChartOpens f g)) hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U', hU', hU'U⟩, hxU'⟩
  · obtain ⟨U', ⟨hU', V, W, hV, hW, eU, eV⟩, hU'U⟩ := i
    rw [map_zero]
    refine injective_app_pullbackRelativeDifferentialsMap f g hU' hV hW eU eV
      (formallySmooth_appLE_of_le_smoothLocus f hU' hV eU (hU'U.trans hU)) ?_
    change (f.pullbackRelativeDifferentialsMap g).app U'
      (((pullback f).obj g.relativeDifferentials).presheaf.map (homOfLE hU'U).op s) = _
    rw [Hom.app_map, hs, map_zero, map_zero]

end Main

end SGA.SGA1.ExposeII
