/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.BaseChangeSections
import SGA.Foundations.Cohomology.IdealPowers
import SGA.Foundations.Cohomology.Pushforward
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# The Rees module on `X ×_A B`

Let `f : X ⟶ Spec A`, `I ⊆ A` an ideal, `B = ⊕ Iⁿ tⁿ ⊆ A[t]` the Rees algebra and
`q_B : X_B = X ×_A B ⟶ X`. For an `𝒪_X`-module `M` the Rees module `⊕ₙ Iⁿ M tⁿ` is the
`𝒪_{X_B}`-module `reesSheaf I f M`, the image of `q_B^* M ⟶ h_* q_t^* M` where
`h : X ×_A A[t] ⟶ X_B` (EGA III 3.3.1). For `M` quasi-coherent and `V ⊆ X` affine:

* `CohomologyAux.reesSecMap`: `Γ(reesSheaf, q_B⁻¹ V) ↪ Γ(M, V)[t]` (injective,
  `reesSecMap_injective`), with image `⊕ Iⁿ Γ(M, V) tⁿ` (`range_reesSecMap`);
* it is semilinear along `reesRingMap : Γ(X_B, q_B⁻¹ V) → Γ(X, V)[t]`, whose image lies in the Rees
  algebra of `I Γ(X, V)` (`reesRingMap_mem`), and compatible with restrictions
  (`reesSecMap_restrict`).
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite Polynomial

namespace AlgebraicGeometry.CohomologyAux

variable {A : CommRingCat.{u}} (I : Ideal A)

/-- The Rees algebra `⊕ Iⁿ tⁿ ⊆ A[t]`. -/
noncomputable abbrev reesRing : CommRingCat.{u} := CommRingCat.of (reesAlgebra I)

/-- `A ⟶ ⊕ Iⁿ tⁿ`. -/
noncomputable abbrev reesMap : A ⟶ reesRing I := CommRingCat.ofHom (algebraMap A (reesAlgebra I))

/-- `⊕ Iⁿ tⁿ ⟶ A[t]`. -/
noncomputable abbrev reesIncl : reesRing I ⟶ CommRingCat.of A[X] :=
  CommRingCat.ofHom (reesAlgebra I).val.toRingHom

lemma reesMap_reesIncl : reesMap I ≫ reesIncl I = polyC A := rfl

variable {X : Scheme.{u}} (f : X ⟶ Spec A)

/-- `X_B = X ×_A B` for the Rees algebra `B`. -/
noncomputable abbrev reesScheme : Scheme.{u} := pullback f (Spec.map (reesMap I))

/-- `X_B ⟶ X`. -/
noncomputable abbrev reesFst : reesScheme I f ⟶ X := pullback.fst _ _

/-- `X_B ⟶ Spec B`. -/
noncomputable abbrev reesSnd : reesScheme I f ⟶ Spec (reesRing I) := pullback.snd _ _

/-- `X ×_A A[t]`. -/
noncomputable abbrev polyScheme : Scheme.{u} := pullback f (Spec.map (polyC A))

/-- `X ×_A A[t] ⟶ Spec A[t]`. -/
noncomputable abbrev polySnd : polyScheme f ⟶ Spec (CommRingCat.of A[X]) := pullback.snd _ _

/-- `X ×_A A[t] ⟶ X ×_A B`, induced by `B ⊆ A[t]`. -/
noncomputable def reesBaseChange : polyScheme f ⟶ reesScheme I f :=
  pullback.map _ _ _ _ (𝟙 X) (Spec.map (reesIncl I)) (𝟙 _) (by simp)
    (by rw [Category.comp_id, ← Spec.map_comp, reesMap_reesIncl])

/-- The projection `X ×_A A[t] ⟶ X`, as a composite through `X_B`. -/
noncomputable abbrev polyFst : polyScheme f ⟶ X := reesBaseChange I f ≫ reesFst I f

lemma polyFst_eq : polyFst I f = pullback.fst f (Spec.map (polyC A)) := by
  simp only [polyFst, reesFst, reesBaseChange, pullback.map, pullback.lift_fst, Category.comp_id]

@[reassoc]
lemma reesBaseChange_reesSnd :
    reesBaseChange I f ≫ reesSnd I f = polySnd f ≫ Spec.map (reesIncl I) := by
  simp only [reesSnd, polySnd, reesBaseChange, pullback.map, pullback.lift_snd]

lemma isPullback_poly : IsPullback (polyFst I f) (polySnd f) f (Spec.map (polyC A)) := by
  rw [polyFst_eq]
  exact IsPullback.of_hasPullback _ _

lemma isPullback_rees : IsPullback (reesFst I f) (reesSnd I f) f (Spec.map (reesMap I)) :=
  IsPullback.of_hasPullback _ _

instance : IsAffineHom (reesFst I f) := isAffineHom_of_isPullback (isPullback_rees I f)

instance : IsAffineHom (polyFst I f) := isAffineHom_of_isPullback (isPullback_poly I f)

instance : IsAffineHom (reesBaseChange I f) := IsAffineHom.of_comp _ (reesFst I f)

variable (M : X.Modules)

/-- The comparison `q_B^* M ⟶ h_* h^* q_B^* M = h_* q_t^* M`, for `h : X ×_A A[t] ⟶ X_B`. -/
noncomputable def reesUnit : (Scheme.Modules.pullback (reesFst I f)).obj M ⟶
    (Scheme.Modules.pushforward (reesBaseChange I f)).obj
      ((Scheme.Modules.pullback (polyFst I f)).obj M) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (reesBaseChange I f)).unit.app _ ≫
    (Scheme.Modules.pushforward (reesBaseChange I f)).map
      ((Scheme.Modules.pullbackComp (reesBaseChange I f) (reesFst I f)).hom.app M)

lemma reesUnit_app_pullbackApp (V : X.Opens) (m : Γ(M, V)) :
    (reesUnit I f M).app (reesFst I f ⁻¹ᵁ V)
      (Scheme.Modules.pullbackApp (reesFst I f) M V m) =
      Scheme.Modules.pullbackApp (polyFst I f) M V m := by
  rw [Scheme.Modules.pullbackApp_comp]
  rfl

/-- **The Rees module** `⊕ₙ Iⁿ M tⁿ`, as a module on `X_B` (EGA III 3.3.1): the image of
`q_B^* M ⟶ h_* q_t^* M`. -/
noncomputable abbrev reesSheaf : (reesScheme I f).Modules := Abelian.image (reesUnit I f M)

section RingMap

variable {V : X.Opens} (hV : IsAffineOpen V)

/-- The ring map `Γ(X_B, q_B⁻¹ V) → Γ(X, V)[t]`. -/
noncomputable def reesRingMap : Γ(reesScheme I f, reesFst I f ⁻¹ᵁ V) →+* Γ(X, V)[X] :=
  ((reesBaseChange I f).app (reesFst I f ⁻¹ᵁ V) ≫
    (baseChangePolynomialIso hV (isPullback_poly I f)).hom).hom

lemma appLE_reesBaseChange :
    (reesFst I f).appLE V (reesFst I f ⁻¹ᵁ V) le_rfl ≫ (reesBaseChange I f).app (reesFst I f ⁻¹ᵁ V)
      = (polyFst I f).appLE V (polyFst I f ⁻¹ᵁ V) le_rfl := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  rfl

lemma reesRingMap_appLE (r : Γ(X, V)) :
    reesRingMap I f hV ((reesFst I f).appLE V (reesFst I f ⁻¹ᵁ V) le_rfl r) = C r :=
  (congrArg (baseChangePolynomialIso hV (isPullback_poly I f)).hom
    (ConcreteCategory.congr_hom (appLE_reesBaseChange I f (V := V)) r)).trans
    (ConcreteCategory.congr_hom (appLE_baseChangePolynomialIso hV (isPullback_poly I f)) r)

lemma appLE_congr_apply {Y Z : Scheme.{u}} {g g' : Y ⟶ Z} (e : g = g') (U : Z.Opens)
    (W : Y.Opens) (h : W ≤ g ⁻¹ᵁ U) (x : Γ(Z, U)) :
    g.appLE U W h x = g'.appLE U W (e ▸ h) x := by
  subst e; rfl

lemma snd_reesBaseChange_apply (b : reesAlgebra I) :
    (reesBaseChange I f).app (reesFst I f ⁻¹ᵁ V) (((Scheme.ΓSpecIso (reesRing I)).inv ≫
      (reesSnd I f).appLE ⊤ (reesFst I f ⁻¹ᵁ V) le_top) b) =
      (polySnd f).appLE ⊤ (polyFst I f ⁻¹ᵁ V) le_top
        ((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv (reesIncl I b)) := by
  have e1 := Scheme.Hom.appLE_comp_appLE (reesBaseChange I f) (reesSnd I f) ⊤
    (reesFst I f ⁻¹ᵁ V) (polyFst I f ⁻¹ᵁ V) le_top le_rfl
  have e3 := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (reesIncl I)) b
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e3
  have s1 : (reesBaseChange I f).app (reesFst I f ⁻¹ᵁ V) (((Scheme.ΓSpecIso (reesRing I)).inv ≫
      (reesSnd I f).appLE ⊤ (reesFst I f ⁻¹ᵁ V) le_top) b) =
      (reesBaseChange I f ≫ reesSnd I f).appLE ⊤ (polyFst I f ⁻¹ᵁ V) le_top
        ((Scheme.ΓSpecIso (reesRing I)).inv b) := by
    rw [Scheme.Hom.app_eq_appLE]
    exact ConcreteCategory.congr_hom e1 _
  have s2 := appLE_congr_apply (reesBaseChange_reesSnd I f) ⊤ (polyFst I f ⁻¹ᵁ V) le_top
    ((Scheme.ΓSpecIso (reesRing I)).inv b)
  have s3 : (polySnd f ≫ Spec.map (reesIncl I)).appLE ⊤ (polyFst I f ⁻¹ᵁ V) le_top
      ((Scheme.ΓSpecIso (reesRing I)).inv b) = (polySnd f).appLE ⊤ (polyFst I f ⁻¹ᵁ V) le_top
        ((Spec.map (reesIncl I)).appTop ((Scheme.ΓSpecIso (reesRing I)).inv b)) :=
    ConcreteCategory.congr_hom (Scheme.Hom.comp_appLE (polySnd f) (Spec.map (reesIncl I)) ⊤
      (polyFst I f ⁻¹ᵁ V) le_top) _
  exact s1.trans (s2.trans (s3.trans (congrArg _ e3.symm)))

lemma reesRingMap_structure (b : reesAlgebra I) :
    reesRingMap I f hV (((Scheme.ΓSpecIso (reesRing I)).inv ≫
      (reesSnd I f).appLE ⊤ (reesFst I f ⁻¹ᵁ V) le_top) b) =
      (b : A[X]).map (structMap f (V := V)).hom :=
  (congrArg (baseChangePolynomialIso hV (isPullback_poly I f)).hom
    (snd_reesBaseChange_apply I f b)).trans
    (ConcreteCategory.congr_hom (structure_baseChangePolynomialIso hV (isPullback_poly I f))
      (reesIncl I b))

/-- The ring map `Γ(X_B, q_B⁻¹ V) → Γ(X, V)[t]` lands in the Rees algebra of `I Γ(X, V)`. -/
lemma reesRingMap_mem (s : Γ(reesScheme I f, reesFst I f ⁻¹ᵁ V)) :
    reesRingMap I f hV s ∈ reesAlgebra (I.map (structMap f (V := V)).hom) := by
  have hcl := CommRingCat.closure_range_union_range_eq_top_of_isPushout
    (isPushout_baseChange (isPullback_rees I f) hV)
  let T : Subring Γ(reesScheme I f, reesFst I f ⁻¹ᵁ V) :=
    (reesAlgebra (I.map (structMap f (V := V)).hom)).toSubring.comap (reesRingMap I f hV)
  have hle : Set.range ((reesFst I f).appLE V (reesFst I f ⁻¹ᵁ V) le_rfl) ∪
      Set.range ((Scheme.ΓSpecIso (reesRing I)).inv ≫
        (reesSnd I f).appLE ⊤ (reesFst I f ⁻¹ᵁ V) le_top) ⊆ T := by
    rintro _ (⟨r, rfl⟩ | ⟨b, rfl⟩)
    · refine Subring.mem_comap.mpr ?_
      rw [Subalgebra.mem_toSubring, reesRingMap_appLE, ← Polynomial.monomial_zero_left]
      exact reesAlgebra.monomial_mem.mpr (by rw [pow_zero, Ideal.one_eq_top]; trivial)
    · refine Subring.mem_comap.mpr ?_
      rw [Subalgebra.mem_toSubring, reesRingMap_structure, mem_reesAlgebra_iff]
      intro i
      rw [Polynomial.coeff_map, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ((mem_reesAlgebra_iff I _).mp b.2 i)
  have : s ∈ T := (Subring.closure_le.mpr hle) (hcl ▸ Subring.mem_top s)
  exact this

end RingMap

section General

open ModuleCat ChangeOfRings

variable {T Y : Scheme.{u}} (g : T ⟶ Y) (N : Y.Modules) [N.IsQuasicoherent] {U : Y.Opens}
  (hU : IsAffineOpen U) (hW : IsAffineOpen (g ⁻¹ᵁ U))

include hU hW in
/-- The sections of `g^* N` over `g⁻¹ U` are generated by the `c • g^* s`. -/
lemma pullbackSections_mem_closure (y : Γ((Scheme.Modules.pullback g).obj N, g ⁻¹ᵁ U)) :
    y ∈ AddSubgroup.closure {x | ∃ (c : Γ(T, g ⁻¹ᵁ U)) (m : Γ(N, U)),
      x = c • Scheme.Modules.pullbackApp g N U m} := by
  rw [← (Scheme.Modules.pullbackSectionsEquiv g N hU hW).symm_apply_apply y]
  generalize Scheme.Modules.pullbackSectionsEquiv g N hU hW y = t
  induction t using TensorProduct.induction_on with
  | zero => erw [map_zero]; exact AddSubgroup.zero_mem _
  | tmul c m =>
    refine AddSubgroup.subset_closure ⟨c, m, ?_⟩
    exact Scheme.Modules.pullbackSectionsEquiv_symm_tmul g N hU hW c m
  | add x y hx hy => erw [map_add]; exact AddSubgroup.add_mem _ hx hy

end General

section PolynomialSmul

open ModuleCat ChangeOfRings

variable {X Y : Scheme.{u}} {f : X ⟶ Spec A} {V : X.Opens} (hV : IsAffineOpen V)
  {g : Y ⟶ X} {g' : Y ⟶ Spec (CommRingCat.of A[X])}
  (H : IsPullback g g' f (Spec.map (polyC A))) (M : X.Modules) [M.IsQuasicoherent]

lemma polynomialTensorEquiv_smul (N : Type u) [AddCommGroup N] [Module Γ(X, V) N]
    (c : Γ(Y, g ⁻¹ᵁ V))
    (t : (extendScalars (g.appLE V (g ⁻¹ᵁ V) le_rfl).hom).obj (ModuleCat.of Γ(X, V) N)) :
    polynomialTensorEquiv hV H N (c • t) =
      (baseChangePolynomialIso hV H).hom c • polynomialTensorEquiv hV H N t := by
  induction t using TensorProduct.induction_on with
  | zero =>
    have h0 : (c • (0 : (extendScalars (g.appLE V (g ⁻¹ᵁ V) le_rfl).hom).obj
        (ModuleCat.of Γ(X, V) N))) = 0 := smul_zero c
    refine (congrArg (polynomialTensorEquiv hV H N) h0).trans ?_
    rw [map_zero]
    exact (smul_zero _).symm.trans (congrArg _ (map_zero _).symm)
  | tmul c' n =>
    erw [ExtendScalars.smul_tmul, polynomialTensorEquiv_tmul, polynomialTensorEquiv_tmul, map_mul,
      mul_smul]
  | add x y hx hy => erw [smul_add, map_add, map_add, hx, hy, smul_add]

lemma pullbackPolynomialSectionsEquiv_smul (c : Γ(Y, g ⁻¹ᵁ V))
    (x : Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ V)) :
    pullbackPolynomialSectionsEquiv hV H M (c • x) =
      (baseChangePolynomialIso hV H).hom c • pullbackPolynomialSectionsEquiv hV H M x := by
  have : IsAffineHom g := isAffineHom_of_isPullback H
  rw [pullbackPolynomialSectionsEquiv, AddEquiv.trans_apply, AddEquiv.trans_apply,
    Scheme.Modules.pullbackSectionsEquiv_smul]
  exact polynomialTensorEquiv_smul hV H Γ(M, V) c _

lemma pullbackPolynomialSectionsEquiv_pullbackApp (m : Γ(M, V)) :
    pullbackPolynomialSectionsEquiv hV H M (Scheme.Modules.pullbackApp g M V m) =
      PolynomialModule.single Γ(X, V) 0 m := by
  rw [← one_smul Γ(Y, g ⁻¹ᵁ V) (Scheme.Modules.pullbackApp g M V m),
    pullbackPolynomialSectionsEquiv_smul_pullbackApp, map_one, one_smul]

end PolynomialSmul

section Sections

variable [M.IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V)

/-- The Rees module `⊕ₙ Iⁿ Γ(M, V) tⁿ ⊆ Γ(M, V)[t]`. -/
def reesSub (V : X.Opens) : AddSubgroup (PolynomialModule Γ(X, V) Γ(M, V)) where
  carrier := {p | ∀ n, p.coeff n ∈ idealV f I V n • (⊤ : Submodule Γ(X, V) Γ(M, V))}
  add_mem' hp hq n := by
    rw [PolynomialModule.coeff_add, Finsupp.add_apply]
    exact Submodule.add_mem _ (hp n) (hq n)
  zero_mem' n := by
    rw [PolynomialModule.coeff_zero, Finsupp.zero_apply]
    exact Submodule.zero_mem _
  neg_mem' {p} hp n := by
    rw [show (-p).coeff = -p.coeff from map_neg PolynomialModule.coeffAddEquiv p,
      Finsupp.neg_apply]
    exact Submodule.neg_mem _ (hp n)

/-- The sections of the Rees sheaf over `q_B⁻¹ V`, as polynomials with coefficients in `Γ(M, V)`. -/
noncomputable def reesSecMap :
    Γ(reesSheaf I f M, reesFst I f ⁻¹ᵁ V) →+ PolynomialModule Γ(X, V) Γ(M, V) :=
  (pullbackPolynomialSectionsEquiv hV (isPullback_poly I f) M).toAddMonoidHom.comp
    ((Abelian.image.ι (reesUnit I f M)).app (reesFst I f ⁻¹ᵁ V)).hom

lemma reesSecMap_factorThruImage (y : Γ((Scheme.Modules.pullback (reesFst I f)).obj M,
    reesFst I f ⁻¹ᵁ V)) :
    reesSecMap I f M hV ((Abelian.factorThruImage (reesUnit I f M)).app (reesFst I f ⁻¹ᵁ V) y) =
      pullbackPolynomialSectionsEquiv hV (isPullback_poly I f) M
        ((reesUnit I f M).app (reesFst I f ⁻¹ᵁ V) y) := by
  have key : (Abelian.image.ι (reesUnit I f M)).app (reesFst I f ⁻¹ᵁ V)
      ((Abelian.factorThruImage (reesUnit I f M)).app (reesFst I f ⁻¹ᵁ V) y) =
      (reesUnit I f M).app (reesFst I f ⁻¹ᵁ V) y :=
    (Scheme.Modules.Hom.comp_app_apply _ _ _ y).symm.trans
      (congrArg (fun φ ↦ Scheme.Modules.Hom.app φ (reesFst I f ⁻¹ᵁ V) y)
        (Abelian.image.fac (reesUnit I f M)))
  exact congrArg (pullbackPolynomialSectionsEquiv hV (isPullback_poly I f) M) key

lemma reesSecMap_gen (c : Γ(reesScheme I f, reesFst I f ⁻¹ᵁ V)) (m : Γ(M, V)) :
    reesSecMap I f M hV ((Abelian.factorThruImage (reesUnit I f M)).app (reesFst I f ⁻¹ᵁ V)
      (c • Scheme.Modules.pullbackApp (reesFst I f) M V m)) =
      reesRingMap I f hV c • PolynomialModule.single Γ(X, V) 0 m := by
  have h1 := reesSecMap_factorThruImage I f M hV
    (c • Scheme.Modules.pullbackApp (reesFst I f) M V m)
  have h2 : (reesUnit I f M).app (reesFst I f ⁻¹ᵁ V)
      (c • Scheme.Modules.pullbackApp (reesFst I f) M V m) =
      @id Γ(polyScheme f, polyFst I f ⁻¹ᵁ V) ((reesBaseChange I f).app (reesFst I f ⁻¹ᵁ V) c) •
        Scheme.Modules.pullbackApp (polyFst I f) M V m := by
    rw [Scheme.Modules.Hom.app_smul, reesUnit_app_pullbackApp]
    rfl
  refine h1.trans ((congrArg _ h2).trans ?_)
  exact pullbackPolynomialSectionsEquiv_smul_pullbackApp hV (isPullback_poly I f) M _ m

lemma reesSecMap_injective : Function.Injective (reesSecMap I f M hV) := by
  have : Mono (Scheme.Modules.Hom.toAbSheaf (Abelian.image.ι (reesUnit I f M))) :=
    (Scheme.Modules.toAbSheafFunctor _).map_mono _
  exact (pullbackPolynomialSectionsEquiv hV (isPullback_poly I f) M).injective.comp
    (CategoryTheory.Sheaf.app_injective_of_mono
      (Scheme.Modules.Hom.toAbSheaf (Abelian.image.ι (reesUnit I f M))) _)

set_option maxRecDepth 4000 in
lemma reesSecMap_smul (c : Γ(reesScheme I f, reesFst I f ⁻¹ᵁ V))
    (z : Γ(reesSheaf I f M, reesFst I f ⁻¹ᵁ V)) :
    reesSecMap I f M hV (c • z) = reesRingMap I f hV c • reesSecMap I f M hV z := by
  have h := Scheme.Modules.Hom.app_smul (Abelian.image.ι (reesUnit I f M)) c z
  exact (congrArg (pullbackPolynomialSectionsEquiv hV (isPullback_poly I f) M) h).trans
    (pullbackPolynomialSectionsEquiv_smul hV (isPullback_poly I f) M
      ((reesBaseChange I f).app (reesFst I f ⁻¹ᵁ V) c) _)

lemma reesSecMap_mem (z : Γ(reesSheaf I f M, reesFst I f ⁻¹ᵁ V)) :
    reesSecMap I f M hV z ∈ reesSub I f M V := by
  have : ((Scheme.Modules.pushforward (reesBaseChange I f)).obj
      ((Scheme.Modules.pullback (polyFst I f)).obj M)).IsQuasicoherent :=
    isQuasicoherent_pushforward _ _
  obtain ⟨y, rfl⟩ := surjective_factorThruImage_app (reesUnit I f M) (hV.preimage (reesFst I f)) z
  let φ : Γ((Scheme.Modules.pullback (reesFst I f)).obj M, reesFst I f ⁻¹ᵁ V) →+
      PolynomialModule Γ(X, V) Γ(M, V) := (reesSecMap I f M hV).comp
    ((Abelian.factorThruImage (reesUnit I f M)).app (reesFst I f ⁻¹ᵁ V)).hom
  change y ∈ (reesSub I f M V).comap φ
  refine (AddSubgroup.closure_le _).mpr ?_ (pullbackSections_mem_closure (reesFst I f) M hV
    (hV.preimage _) y)
  rintro _ ⟨c, m, rfl⟩ n
  change (reesSecMap I f M hV ((Abelian.factorThruImage (reesUnit I f M)).app _
    (c • Scheme.Modules.pullbackApp (reesFst I f) M V m))).coeff n ∈ _
  rw [reesSecMap_gen, PolynomialModule.smul_single_apply]
  simp only [Nat.zero_le, ↓reduceIte, Nat.sub_zero]
  refine Submodule.smul_mem_smul ?_ Submodule.mem_top
  have hmem := (mem_reesAlgebra_iff _ _).mp (reesRingMap_mem I f hV c) n
  rwa [← Ideal.map_pow] at hmem

lemma single_smul_mem_range_reesSecMap (n : ℕ) (r : Γ(X, V)) (hr : r ∈ idealV f I V n)
    (m : Γ(M, V)) :
    PolynomialModule.single Γ(X, V) n (r • m) ∈ (reesSecMap I f M hV).range := by
  rw [idealV, Ideal.map] at hr
  induction hr using Submodule.span_induction generalizing m with
  | mem r hr =>
    obtain ⟨a, ha, rfl⟩ := hr
    let b : reesAlgebra I := ⟨Polynomial.monomial n a, reesAlgebra.monomial_mem.mpr ha⟩
    refine ⟨(Abelian.factorThruImage (reesUnit I f M)).app (reesFst I f ⁻¹ᵁ V)
      ((((Scheme.ΓSpecIso (reesRing I)).inv ≫ (reesSnd I f).appLE ⊤ (reesFst I f ⁻¹ᵁ V)
        le_top) b) • Scheme.Modules.pullbackApp (reesFst I f) M V m), ?_⟩
    rw [reesSecMap_gen, reesRingMap_structure]
    change (Polynomial.monomial n a).map _ • _ = _
    rw [Polynomial.map_monomial, PolynomialModule.monomial_smul_single, add_zero]
  | zero =>
    rw [zero_smul, PolynomialModule.single_zero]
    exact AddSubgroup.zero_mem _
  | add r₁ r₂ _ _ h₁ h₂ =>
    rw [add_smul, PolynomialModule.single_add]
    exact AddSubgroup.add_mem _ (h₁ m) (h₂ m)
  | smul c r _ h =>
    rw [smul_eq_mul, mul_comm, mul_smul]
    exact h (c • m)

lemma single_mem_range_reesSecMap (n : ℕ) (x : Γ(M, V))
    (hx : x ∈ idealV f I V n • (⊤ : Submodule Γ(X, V) Γ(M, V))) :
    PolynomialModule.single Γ(X, V) n x ∈ (reesSecMap I f M hV).range := by
  refine Submodule.smul_induction_on hx (fun r hr m _ ↦ ?_) (fun a b ha hb ↦ ?_)
  · exact single_smul_mem_range_reesSecMap I f M hV n r hr m
  · rw [PolynomialModule.single_add]
    exact AddSubgroup.add_mem _ ha hb

lemma range_reesSecMap : (reesSecMap I f M hV).range = reesSub I f M V := by
  refine le_antisymm (fun p ⟨z, hz⟩ ↦ hz ▸ reesSecMap_mem I f M hV z) fun p hp ↦ ?_
  have hp' : p = ∑ n ∈ p.coeff.support, PolynomialModule.single Γ(X, V) n (p.coeff n) := by
    apply PolynomialModule.ext
    rw [PolynomialModule.coeff_sum]
    simp only [PolynomialModule.coeff_single]
    exact (Finsupp.sum_single p.coeff).symm
  rw [hp']
  exact AddSubgroup.sum_mem _ fun n _ ↦ single_mem_range_reesSecMap I f M hV n _ (hp n)

section Naturality

variable {V' : X.Opens} (hV' : IsAffineOpen V') (hle : V' ≤ V)

omit [M.IsQuasicoherent] in
lemma reesRingMap_restrict (c : Γ(reesScheme I f, reesFst I f ⁻¹ᵁ V)) :
    reesRingMap I f hV' ((reesScheme I f).presheaf.map
      (homOfLE ((reesFst I f).preimage_mono hle)).op c) =
      (reesRingMap I f hV c).map (X.presheaf.map (homOfLE hle).op).hom := by
  have hcl := CommRingCat.closure_range_union_range_eq_top_of_isPushout
    (isPushout_baseChange (isPullback_rees I f) hV)
  let L : Γ(reesScheme I f, reesFst I f ⁻¹ᵁ V) →+* Γ(X, V')[X] := (reesRingMap I f hV').comp
    ((reesScheme I f).presheaf.map (homOfLE ((reesFst I f).preimage_mono hle)).op).hom
  let R : Γ(reesScheme I f, reesFst I f ⁻¹ᵁ V) →+* Γ(X, V')[X] :=
    (Polynomial.mapRingHom (X.presheaf.map (homOfLE hle).op).hom).comp (reesRingMap I f hV)
  have hEq : Set.EqOn L R (Set.range ((reesFst I f).appLE V (reesFst I f ⁻¹ᵁ V) le_rfl) ∪
      Set.range ((Scheme.ΓSpecIso (reesRing I)).inv ≫
        (reesSnd I f).appLE ⊤ (reesFst I f ⁻¹ᵁ V) le_top)) := by
    rintro _ (⟨r, rfl⟩ | ⟨b, rfl⟩)
    · simp only [L, R, RingHom.comp_apply, Polynomial.coe_mapRingHom]
      rw [reesRingMap_appLE, Polynomial.map_C, ← ConcreteCategory.comp_apply,
        Scheme.Hom.appLE_map, ← reesRingMap_appLE I f hV' (X.presheaf.map (homOfLE hle).op r),
        ← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE]
    · simp only [L, R, RingHom.comp_apply, Polynomial.coe_mapRingHom]
      have e1 := ConcreteCategory.congr_hom (Scheme.Hom.appLE_map (reesSnd I f)
        (le_top : reesFst I f ⁻¹ᵁ V ≤ reesSnd I f ⁻¹ᵁ ⊤)
        (homOfLE ((reesFst I f).preimage_mono hle)).op) ((Scheme.ΓSpecIso (reesRing I)).inv b)
      rw [reesRingMap_structure, Polynomial.map_map]
      refine (congrArg (reesRingMap I f hV') e1).trans ?_
      refine (reesRingMap_structure I f hV' b).trans ?_
      congr 1
      have e2 := Scheme.Hom.appLE_map f (show V ≤ f ⁻¹ᵁ ⊤ from le_top) (homOfLE hle).op
      simp only [structMap, ← CommRingCat.hom_comp, Category.assoc]
      rw [e2]
  have := RingHom.eqOn_set_closure hEq (hcl ▸ Subring.mem_top c)
  exact this

lemma reesSecMap_restrict (z : Γ(reesSheaf I f M, reesFst I f ⁻¹ᵁ V)) (n : ℕ) :
    (reesSecMap I f M hV' ((reesSheaf I f M).presheaf.map
      (homOfLE ((reesFst I f).preimage_mono hle)).op z)).coeff n =
      M.presheaf.map (homOfLE hle).op ((reesSecMap I f M hV z).coeff n) := by
  have : ((Scheme.Modules.pushforward (reesBaseChange I f)).obj
      ((Scheme.Modules.pullback (polyFst I f)).obj M)).IsQuasicoherent :=
    isQuasicoherent_pushforward _ _
  obtain ⟨y, rfl⟩ := surjective_factorThruImage_app (reesUnit I f M) (hV.preimage (reesFst I f)) z
  let φ₁ : Γ((Scheme.Modules.pullback (reesFst I f)).obj M, reesFst I f ⁻¹ᵁ V) →+ Γ(M, V') :=
    { toFun := fun y ↦ (reesSecMap I f M hV' ((reesSheaf I f M).presheaf.map
        (homOfLE ((reesFst I f).preimage_mono hle)).op
        ((Abelian.factorThruImage (reesUnit I f M)).app (reesFst I f ⁻¹ᵁ V) y))).coeff n
      map_zero' := by simp
      map_add' := fun a b ↦ by simp [map_add] }
  let φ₂ : Γ((Scheme.Modules.pullback (reesFst I f)).obj M, reesFst I f ⁻¹ᵁ V) →+ Γ(M, V') :=
    { toFun := fun y ↦ M.presheaf.map (homOfLE hle).op ((reesSecMap I f M hV
        ((Abelian.factorThruImage (reesUnit I f M)).app (reesFst I f ⁻¹ᵁ V) y)).coeff n)
      map_zero' := by simp
      map_add' := fun a b ↦ by simp [map_add] }
  change φ₁ y = φ₂ y
  refine (AddSubgroup.closure_le (AddMonoidHom.eqLocus φ₁ φ₂)).mpr ?_
    (pullbackSections_mem_closure (reesFst I f) M hV (hV.preimage _) y)
  rintro _ ⟨c, m, rfl⟩
  change φ₁ _ = φ₂ _
  simp only [φ₁, φ₂, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  have e3 : ((Scheme.Modules.pullback (reesFst I f)).obj M).presheaf.map
      (homOfLE ((reesFst I f).preimage_mono hle)).op
        (Scheme.Modules.pullbackApp (reesFst I f) M V m) =
      Scheme.Modules.pullbackApp (reesFst I f) M V' (M.presheaf.map (homOfLE hle).op m) :=
    (Scheme.Modules.pullbackApp_map _ _ _ _).symm
  rw [← CohomologyAux.hom_app_presheaf_map, Scheme.Modules.map_smul, e3, reesSecMap_gen,
    reesSecMap_gen,
    PolynomialModule.smul_single_apply, PolynomialModule.smul_single_apply]
  simp only [Nat.zero_le, ↓reduceIte, Nat.sub_zero]
  rw [reesRingMap_restrict I f hV hV' hle, Polynomial.coeff_map, Scheme.Modules.map_smul]

end Naturality

end Sections

end AlgebraicGeometry.CohomologyAux
