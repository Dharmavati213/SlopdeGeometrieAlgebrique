/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.LocallyFreeAlgebraization


/-!
# Algebraization of algebra structures

Let `A` be a noetherian `I`-adically complete ring, `X` proper over `Spec A`, and `B` a coherent
`𝒪_X`-module with projective sections over affine opens (e.g. the algebraization of a locally free
adic system, `SGA.Foundations.Cohomology.LocallyFreeAlgebraization`) with compatible isomorphisms
`B / I^{n+1} B ≅ Gₙ`. Compatible commutative algebra structures on the `Gₙ` come from a commutative
algebra structure on `B` (EGA III 5.4.1, for finite algebras).

An algebra structure on an `𝒪_X`-module `M` (`ModuleAlgebra`) is a multiplication
`M ⟶ ℋom(M, M)` and a unit section, commutative, associative and unital on the sections over all
opens. We use the internal hom `ℋom` of `SGA.Foundations.Differentials.SheafHom` and its
functoriality (`sheafHomPrecomp`, `sheafHomEval`, `sheafHomComp`).

* `mem_pow_smul_top_of_forall_apply_mem`: `Hom(P, Jᵏ N) = Jᵏ Hom(P, N)` for `P` finite projective;
* `eq_of_comp_sheafHomPostcomp_eq`: morphisms into `ℋom(B, K)` are determined modulo all the
  `I^{n+1}`;
* `isIso_algκbar`: `ℋom(B, B) / I^{n+1} ≅ ℋom(B, B / I^{n+1} B)`;
* `exists_mul_algebraization`, `exists_one_algebraization`: the multiplication and the unit
  algebraize, by the existence and uniqueness halves of the theorem of formal functions;
* `mul_comm_algebraization`, `mul_assoc_algebraization`, `one_mul_algebraization`,
  `exists_moduleAlgebra_algebraization`: the axioms hold on `B`, being identities between morphisms
  of coherent modules which hold modulo every `I^{n+1}`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.CohomologyAux

section LinearAlgebra

variable {R : Type u} [CommRing R] (J : Ideal R)

/-- **`Hom(P, Jᵏ N) = Jᵏ Hom(P, N)` for `P` finite projective**. -/
theorem mem_pow_smul_top_of_forall_apply_mem {P N : Type*} [AddCommGroup P]
    [Module R P] [Module.Finite R P] [Module.Projective R P] [AddCommGroup N] [Module R N]
    (k : ℕ) (φ : P →ₗ[R] N) (hφ : ∀ p, φ p ∈ (J ^ k • ⊤ : Submodule R N)) :
    φ ∈ (J ^ k • ⊤ : Submodule R (P →ₗ[R] N)) := by
  obtain ⟨b, π, hπ⟩ := Module.Finite.exists_fin' R P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  -- `φ ∘ π` corresponds to the tuple `(φ (π eᵢ))ᵢ`
  let e : ((Fin b → R) →ₗ[R] N) ≃ₗ[R] (Fin b → N) := LinearEquiv.piRing R N (Fin b) R
  have h1 : e (φ ∘ₗ π) ∈ (J ^ k • ⊤ : Submodule R (Fin b → N)) :=
    pi_mem_pow_smul_top J k _ fun i ↦ by
      rw [LinearEquiv.piRing_apply]
      exact hφ _
  have h2 : φ ∘ₗ π ∈ (J ^ k • ⊤ : Submodule R ((Fin b → R) →ₗ[R] N)) := by
    have := mem_smul_top_of_linearMap _ e.symm.toLinearMap h1
    rwa [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at this
  have h3 := mem_smul_top_of_linearMap _ (LinearMap.lcomp R N s) h2
  have e3 : LinearMap.lcomp R N s (φ ∘ₗ π) = φ := by
    ext p
    change φ (π (s p)) = φ p
    rw [← LinearMap.comp_apply π s, hs, LinearMap.id_apply]
  rwa [e3] at h3

end LinearAlgebra

section HomMorphisms

variable {X : Scheme.{u}}

open Scheme.Modules

/-- Precomposition of `φ : HomOn M N U` with a morphism `g : M' ⟶ M`. -/
def homOnPrecomp {M M' N : X.Modules} {U : X.Opens} (φ : HomOn M N U) (g : M' ⟶ M) :
    HomOn M' N U where
  app V hV := φ.app V hV ∘ₗ appLinearMap g V
  naturality hWV hV m := by
    change φ.app _ _ (g.app _ (M'.presheaf.map _ m)) = N.presheaf.map _ (φ.app _ _ (g.app _ m))
    rw [hom_app_presheaf_map, φ.naturality]

@[simp]
lemma homOnPrecomp_app {M M' N : X.Modules} {U : X.Opens} (φ : HomOn M N U) (g : M' ⟶ M)
    (V : X.Opens) (hV : V ≤ U) (m : Γ(M', V)) :
    (homOnPrecomp φ g).app V hV m = φ.app V hV (g.app V m) :=
  rfl

/-- Precomposition `ℋom(M, N) ⟶ ℋom(M', N)` with a morphism `g : M' ⟶ M`. -/
def sheafHomPrecomp {M M' N : X.Modules} (g : M' ⟶ M) : sheafHom M N ⟶ sheafHom M' N :=
  ⟨_root_.PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun := fun φ : HomOn M N U.unop ↦ homOnPrecomp φ g
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      naturality U V i := by ext φ; rfl }
    fun U r φ ↦ rfl⟩

lemma sheafHomPrecomp_app {M M' N : X.Modules} (g : M' ⟶ M) (U : X.Opens)
    (φ : Γ(sheafHom M N, U)) :
    ((sheafHomPrecomp g).app U φ : HomOn M' N U) = homOnPrecomp (φ : HomOn M N U) g :=
  rfl

/-- Evaluation at a section `m` of `M` over `U`, a section of `ℋom(ℋom(M, N), N)` over `U`. -/
def homOnEval {M N : X.Modules} {U : X.Opens} (m : Γ(M, U)) : HomOn (sheafHom M N) N U where
  app V hV :=
    { toFun := fun φ : Γ(sheafHom M N, V) ↦
        (φ : HomOn M N V).app V le_rfl (M.presheaf.map (homOfLE hV).op m)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r φ ↦ by
        change X.presheaf.map (homOfLE (le_refl V)).op r •
            (φ : HomOn M N V).app V le_rfl (M.presheaf.map (homOfLE hV).op m) =
          r • (φ : HomOn M N V).app V le_rfl (M.presheaf.map (homOfLE hV).op m)
        rw [presheaf_map_self] }
  naturality {V W} hWV hV φ := by
    change (φ : HomOn M N V).app W hWV (M.presheaf.map (homOfLE (hWV.trans hV)).op m) =
      N.presheaf.map (homOfLE hWV).op ((φ : HomOn M N V).app V le_rfl
        (M.presheaf.map (homOfLE hV).op m))
    rw [← (φ : HomOn M N V).naturality hWV le_rfl,
      modules_map_map_apply M (homOfLE hWV) (homOfLE hV) (homOfLE (hWV.trans hV))]

lemma homOnEval_app {M N : X.Modules} {U : X.Opens} (m : Γ(M, U)) (V : X.Opens) (hV : V ≤ U)
    (φ : Γ(sheafHom M N, V)) :
    (homOnEval (N := N) m).app V hV φ =
      (φ : HomOn M N V).app V le_rfl (M.presheaf.map (homOfLE hV).op m) :=
  rfl

/-- Evaluation `M ⟶ ℋom(ℋom(M, N), N)`. -/
def sheafHomEval (M N : X.Modules) : M ⟶ sheafHom (sheafHom M N) N :=
  ⟨_root_.PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun := fun m : Γ(M, U.unop) ↦ homOnEval m
          map_zero' := HomOn.ext (funext fun V ↦ funext fun hV ↦ LinearMap.ext fun φ ↦ by
            change (φ : HomOn M N V).app V le_rfl (M.presheaf.map (homOfLE hV).op 0) = 0
            rw [map_zero, map_zero])
          map_add' := fun (m m' : Γ(M, U.unop)) ↦ HomOn.ext (funext fun V ↦ funext fun hV ↦
            LinearMap.ext fun φ ↦ by
              change (φ : HomOn M N V).app V le_rfl (M.presheaf.map (homOfLE hV).op (m + m')) =
                (φ : HomOn M N V).app V le_rfl (M.presheaf.map (homOfLE hV).op m) +
                  (φ : HomOn M N V).app V le_rfl (M.presheaf.map (homOfLE hV).op m')
              rw [map_add, map_add]) }
      naturality U U' i := by
        ext (m : Γ(M, U.unop))
        refine HomOn.ext (funext fun V ↦ funext fun hV ↦ LinearMap.ext fun φ ↦ ?_)
        change (φ : HomOn M N V).app V le_rfl
            (M.presheaf.map (homOfLE hV).op (M.presheaf.map (homOfLE i.unop.le).op m)) =
          (φ : HomOn M N V).app V le_rfl (M.presheaf.map (homOfLE (hV.trans i.unop.le)).op m)
        rw [modules_map_map_apply M (homOfLE hV) (homOfLE i.unop.le)
          (homOfLE (hV.trans i.unop.le))] }
    fun U (r : Γ(X, U.unop)) (m : Γ(M, U.unop)) ↦ HomOn.ext (funext fun V ↦ funext fun hV ↦
      LinearMap.ext fun φ ↦ by
        change (φ : HomOn M N V).app V le_rfl (M.presheaf.map (homOfLE hV).op (r • m)) =
          X.presheaf.map (homOfLE hV).op r • (φ : HomOn M N V).app V le_rfl
            (M.presheaf.map (homOfLE hV).op m)
        rw [Scheme.Modules.map_smul, LinearMap.map_smul])⟩

lemma sheafHomEval_app (M N : X.Modules) (U : X.Opens) (m : Γ(M, U)) :
    ((sheafHomEval M N).app U m : HomOn (sheafHom M N) N U) = homOnEval m :=
  rfl

/-- Composition of sections of `ℋom`. -/
def homOnCompose {M N K : X.Modules} {V : X.Opens} (T : HomOn N K V) (S : HomOn M N V) :
    HomOn M K V where
  app W hW := T.app W hW ∘ₗ S.app W hW
  naturality hWV hV m := by
    change T.app _ _ (S.app _ _ (M.presheaf.map _ m)) = K.presheaf.map _ (T.app _ _ (S.app _ _ m))
    rw [S.naturality, T.naturality]

/-- Composition with a section `T` of `ℋom(N, K)`, a section of `ℋom(ℋom(M, N), ℋom(M, K))`. -/
def homOnComp {M N K : X.Modules} {U : X.Opens} (T : HomOn N K U) :
    HomOn (sheafHom M N) (sheafHom M K) U where
  app V hV :=
    { toFun := fun S : Γ(sheafHom M N, V) ↦ (homOnCompose (T.restrict hV) (S : HomOn M N V) :
        Γ(sheafHom M K, V))
      map_add' := fun _ _ ↦ HomOn.ext (funext fun W ↦ funext fun hW ↦ LinearMap.ext fun _ ↦
        (T.app W (hW.trans hV)).map_add _ _)
      map_smul' := fun _ _ ↦ HomOn.ext (funext fun W ↦ funext fun hW ↦ LinearMap.ext fun _ ↦
        (T.app W (hW.trans hV)).map_smul _ _) }
  naturality _ _ _ := rfl

/-- Composition `ℋom(N, K) ⟶ ℋom(ℋom(M, N), ℋom(M, K))`. -/
def sheafHomComp (M N K : X.Modules) : sheafHom N K ⟶ sheafHom (sheafHom M N) (sheafHom M K) :=
  ⟨_root_.PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun := fun T : HomOn N K U.unop ↦ homOnComp T
          map_zero' := HomOn.ext (funext fun V ↦ funext fun hV ↦ LinearMap.ext fun S ↦
            HomOn.ext (funext fun W ↦ funext fun hW ↦ LinearMap.ext fun m ↦ rfl))
          map_add' := fun _ _ ↦ HomOn.ext (funext fun V ↦ funext fun hV ↦ LinearMap.ext fun S ↦
            HomOn.ext (funext fun W ↦ funext fun hW ↦ LinearMap.ext fun m ↦ rfl)) }
      naturality U V i := by
        ext T
        exact HomOn.ext (funext fun W ↦ funext fun hW ↦ LinearMap.ext fun S ↦
          HomOn.ext (funext fun W' ↦ funext fun hW' ↦ LinearMap.ext fun m ↦ rfl)) }
    fun U (r : Γ(X, U.unop)) T ↦ HomOn.ext (funext fun V ↦ funext fun hV ↦ LinearMap.ext fun S ↦
      HomOn.ext (funext fun W ↦ funext fun hW ↦ LinearMap.ext fun m ↦ by
        change X.presheaf.map (homOfLE (hW.trans hV)).op r •
            T.app W _ ((S : HomOn M N V).app W hW m) =
          X.presheaf.map (homOfLE hW).op (X.presheaf.map (homOfLE hV).op r) •
            T.app W _ ((S : HomOn M N V).app W hW m)
        congr 1
        exact (presheaf_map_map hV hW r).symm))⟩

end HomMorphisms

section ModuleAlgebra

variable {X : Scheme.{u}}

open Scheme.Modules

/-- The value of a section `φ.app U x` of `ℋom(N, K)` over an open `V ⊆ U` is the value of the
section `φ.app V (x|_V)` over `V`. -/
lemma homOn_app_res {M N K : X.Modules} (φ : M ⟶ sheafHom N K) {U V : X.Opens} (hV : V ≤ U)
    (x : Γ(M, U)) (y : Γ(N, V)) :
    ((φ.app U x : Γ(sheafHom N K, U)) : HomOn N K U).app V hV y =
      ((φ.app V (M.presheaf.map (homOfLE hV).op x) : Γ(sheafHom N K, V)) : HomOn N K V).app V
        le_rfl y := by
  rw [hom_app_presheaf_map]
  rfl

/-- The multiplication `x * y` on the sections over `U` defined by `m : M ⟶ ℋom(M, M)`. -/
def mulApp {M : X.Modules} (m : M ⟶ sheafHom M M) (U : X.Opens) (x y : Γ(M, U)) : Γ(M, U) :=
  ((m.app U x : Γ(sheafHom M M, U)) : HomOn M M U).app U le_rfl y

lemma mulApp_eq {M : X.Modules} (m : M ⟶ sheafHom M M) {U V : X.Opens} (hV : V ≤ U)
    (x : Γ(M, U)) (y : Γ(M, V)) :
    ((m.app U x : Γ(sheafHom M M, U)) : HomOn M M U).app V hV y =
      mulApp m V (M.presheaf.map (homOfLE hV).op x) y :=
  homOn_app_res m hV x y

lemma mulApp_res {M : X.Modules} (m : M ⟶ sheafHom M M) {U V : X.Opens} (hV : V ≤ U)
    (x y : Γ(M, U)) :
    M.presheaf.map (homOfLE hV).op (mulApp m U x y) =
      mulApp m V (M.presheaf.map (homOfLE hV).op x) (M.presheaf.map (homOfLE hV).op y) := by
  rw [mulApp, ← ((m.app U x : Γ(sheafHom M M, U)) : HomOn M M U).naturality hV le_rfl,
    homOn_app_res]
  rfl

/-- A commutative algebra structure on an `𝒪_X`-module `M`: a multiplication `M ⟶ ℋom(M, M)` and
a global unit section, commutative, associative and unital on the sections over every open. -/
structure ModuleAlgebra (M : X.Modules) where
  /-- The multiplication. -/
  mul : M ⟶ sheafHom M M
  /-- The unit. -/
  one : Γ(M, ⊤)
  mul_comm : ∀ (U : X.Opens) (x y : Γ(M, U)), mulApp mul U x y = mulApp mul U y x
  mul_assoc : ∀ (U : X.Opens) (x y z : Γ(M, U)),
    mulApp mul U (mulApp mul U x y) z = mulApp mul U x (mulApp mul U y z)
  one_mul : ∀ (U : X.Opens) (x : Γ(M, U)),
    mulApp mul U (M.presheaf.map (homOfLE le_top).op one) x = x

end ModuleAlgebra

section Separation

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec A)

open Scheme.Modules

omit [IsNoetherianRing A] in
/-- A section `t` of `ℋom(B, K)` over an affine open, `B` with finite projective sections, whose
composite with `ρ : K ⟶ K'` vanishes lies in `Jᵏ ℋom(B, K)` if `ker ρ ⊆ Jᵏ K` there. -/
lemma mem_pow_smul_of_sheafHomPostcomp_app_eq_zero [IsLocallyNoetherian X] {B K K' : X.Modules}
    [B.IsCoherent] {V : X.Opens} (hV : IsAffineOpen V) [Module.Projective Γ(X, V) Γ(B, V)]
    (ρ : K ⟶ K') (k : ℕ)
    (hρ : ∀ x : Γ(K, V), ρ.app V x = 0 → x ∈ (idealV f I V 1 ^ k • ⊤ : Submodule Γ(X, V) Γ(K, V)))
    (t : Γ(sheafHom B K, V)) (ht : (sheafHomPostcomp ρ).app V t = 0) :
    t ∈ (idealV f I V 1 ^ k • ⊤ : Submodule Γ(X, V) Γ(sheafHom B K, V)) := by
  have : B.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : B.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  have : Module.Finite Γ(X, V) Γ(B, V) := finite_sections_of_isFiniteType B hV
  have h1 : sheafHomAffineEquiv hV B K t ∈
      (idealV f I V 1 ^ k • ⊤ : Submodule Γ(X, V) (Γ(B, V) →ₗ[Γ(X, V)] Γ(K, V))) :=
    mem_pow_smul_top_of_forall_apply_mem _ k _ fun c ↦ hρ _ (by
      have := congrArg (sheafHomAffineEquiv hV B K') ht
      rw [sheafHomAffineEquiv_postcomp, map_zero] at this
      exact LinearMap.congr_fun this c)
  have h2 := mem_smul_top_of_linearMap _ (sheafHomAffineEquiv hV B K).symm.toLinearMap h1
  rwa [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h2

variable [IsAdicComplete I A] [IsProper f]

/-- **Separation for morphisms into `ℋom(B, K)`**: over a complete base, two morphisms
`Φ, Ψ : F ⟶ ℋom(B, K)` of coherent modules (`B` with projective sections over affine opens)
agreeing after composition with a family `ρₙ : K ⟶ K'ₙ` whose kernels on affine opens lie in
`I^{n+1} K` are equal. -/
theorem eq_of_comp_sheafHomPostcomp_eq {F B K : X.Modules} [F.IsCoherent] [B.IsCoherent]
    [K.IsCoherent] (hB : ∀ {V : X.Opens}, IsAffineOpen V → Module.Projective Γ(X, V) Γ(B, V))
    {K' : ℕ → X.Modules} (ρ : ∀ n, K ⟶ K' n)
    (hρ : ∀ (n : ℕ) {V : X.Opens} (_ : IsAffineOpen V) (x : Γ(K, V)), (ρ n).app V x = 0 →
      x ∈ (idealV f I V 1 ^ (n + 1) • ⊤ : Submodule Γ(X, V) Γ(K, V)))
    {Φ Ψ : F ⟶ sheafHom B K}
    (h : ∀ n, Φ ≫ sheafHomPostcomp (ρ n) = Ψ ≫ sheafHomPostcomp (ρ n)) :
    Φ = Ψ := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : (sheafHom B K).IsCoherent := isCoherent_sheafHom B K
  have : (sheafHom B K).IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : F.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  refine eq_of_comp_toQuotientIdealPow_eq I f fun n ↦ ?_
  rw [← sub_eq_zero, ← Preadditive.sub_comp]
  refine hom_ext_of_affine fun V hV a ↦ ?_
  change ((sheafHom B K).toQuotientIdealPow f I n).app V ((Φ - Ψ).app V a) = 0
  rw [toQuotientIdealPow_app_eq_zero_iff' I f _ hV]
  have := hB hV
  refine mem_pow_smul_of_sheafHomPostcomp_app_eq_zero I f hV (ρ n) (n + 1) (hρ n hV) _ ?_
  rw [← Scheme.Modules.Hom.comp_app_apply, Preadditive.sub_comp, h n, sub_self]
  rfl

end Separation

section Algebraization

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {X : Scheme.{u}} (f : X ⟶ Spec A) [IsProper f]

open Scheme.Modules

variable {B : X.Modules} {G : AdicSystem I f} (e : ∀ n, B.quotientIdealPow f I n ≅ G.obj n)

/-- The reductions `B ⟶ B / I^{n+1} B ≅ Gₙ`. -/
def algRed (n : ℕ) : B ⟶ G.obj n := B.toQuotientIdealPow f I n ≫ (e n).hom

omit [IsNoetherianRing A] [IsAdicComplete I A] [IsProper f] in
include e in
lemma algRed_comp
    (he : ∀ n, (e (n + 1)).hom ≫ G.map n = B.quotientIdealPowMap f I n ≫ (e n).hom) (n : ℕ) :
    algRed I f e (n + 1) ≫ G.map n = algRed I f e n := by
  rw [algRed, algRed, Category.assoc, he, Scheme.Modules.toQuotientIdealPow_comp_map_assoc]

omit [IsAdicComplete I A] [IsProper f] in
lemma algRed_app_eq_zero [B.IsQuasicoherent] (n : ℕ) {V : X.Opens} (hV : IsAffineOpen V)
    (x : Γ(B, V)) (hx : (algRed I f e n).app V x = 0) :
    x ∈ (idealV f I V 1 ^ (n + 1) • ⊤ : Submodule Γ(X, V) Γ(B, V)) := by
  rw [← quotientIdealPow_app_eq_zero_iff I f B n hV]
  have := congrArg ((e n).inv.app V) hx
  rw [algRed, Scheme.Modules.Hom.comp_app_apply, ← Scheme.Modules.Hom.comp_app_apply,
    Iso.hom_inv_id, map_zero] at this
  exact this

omit [IsAdicComplete I A] [IsProper f] in
lemma algRed_app_surjective [B.IsQuasicoherent] (n : ℕ) {V : X.Opens} (hV : IsAffineOpen V) :
    Function.Surjective ((algRed I f e n).app V) := by
  intro y
  obtain ⟨z, hz⟩ := toQuotientIdealPow_app_surjective I f n hV (M := B) ((e n).inv.app V y)
  refine ⟨z, ?_⟩
  rw [algRed, Scheme.Modules.Hom.comp_app_apply, hz, ← Scheme.Modules.Hom.comp_app_apply,
    Iso.inv_hom_id]
  rfl

end Algebraization

section AlgebraizationMul

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec A)

open Scheme.Modules

variable {B : X.Modules} {G : AdicSystem I f} (e : ∀ n, B.quotientIdealPow f I n ≅ G.obj n)
  (alg : ∀ n, ModuleAlgebra (G.obj n))

/-- The multiplications of the `Gₙ`, pulled back to `B`: `b ↦ (c ↦ b̄ c̄)`. -/
def algV (n : ℕ) : B ⟶ sheafHom B (G.obj n) :=
  algRed I f e n ≫ (alg n).mul ≫ sheafHomPrecomp (algRed I f e n)

omit [IsNoetherianRing A] in
lemma algV_app (n : ℕ) {U V : X.Opens} (hV : V ≤ U) (b : Γ(B, U)) (c : Γ(B, V)) :
    (((algV I f e alg n).app U b : Γ(sheafHom B (G.obj n), U)) : HomOn B (G.obj n) U).app V hV c =
      mulApp (alg n).mul V ((algRed I f e n).app V (B.presheaf.map (homOfLE hV).op b))
        ((algRed I f e n).app V c) := by
  change (((alg n).mul.app U ((algRed I f e n).app U b) : Γ(sheafHom (G.obj n) (G.obj n), U)) :
    HomOn (G.obj n) (G.obj n) U).app V hV ((algRed I f e n).app V c) = _
  rw [homOn_app_res, ← hom_app_presheaf_map]
  rfl

/-- Postcomposition with the reduction `B ⟶ Gₙ`. -/
abbrev algκ (n : ℕ) : sheafHom B B ⟶ sheafHom B (G.obj n) := sheafHomPostcomp (algRed I f e n)

omit [IsNoetherianRing A] in
lemma smulA_sheafHom_eq_zero (n : ℕ) {a : A} (ha : a ∈ I ^ (n + 1)) :
    smulA (sheafHom B (G.obj n)) f a = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext φ
  refine HomOn.ext (funext fun V ↦ funext fun hV ↦ LinearMap.ext fun m ↦ ?_)
  change ((smulA (sheafHom B (G.obj n)) f a).app U φ : HomOn B (G.obj n) U).app V hV m = 0
  rw [smulA_app]
  change X.presheaf.map (homOfLE hV).op (structMapV f U a) • (φ : HomOn B (G.obj n) U).app V hV m
    = 0
  rw [AdicSystem.structMapV_res, ← smulA_app, G.smulA_eq_zero n ha]
  rfl

/-- `ℋom(B, B) / I^{n+1} ⟶ ℋom(B, Gₙ)`. -/
def algκbar (n : ℕ) : (sheafHom B B).quotientIdealPow f I n ⟶ sheafHom B (G.obj n) :=
  descQuotientIdealPow I f n (algκ I f e n) fun _ ha ↦ smulA_sheafHom_eq_zero I f n ha

omit [IsNoetherianRing A] in
@[reassoc (attr := simp)]
lemma toQuotientIdealPow_algκbar (n : ℕ) :
    (sheafHom B B).toQuotientIdealPow f I n ≫ algκbar I f e n = algκ I f e n :=
  toQuotientIdealPow_descQuotientIdealPow I f n _ _

/-- For `B` with finite projective sections, `ℋom(B, B) / I^{n+1} ≅ ℋom(B, B / I^{n+1} B)`. -/
lemma isIso_algκbar [IsLocallyNoetherian X] [B.IsCoherent]
    (hB : ∀ {V : X.Opens}, IsAffineOpen V → Module.Projective Γ(X, V) Γ(B, V)) (n : ℕ) :
    IsIso (algκbar I f e n) := by
  have : B.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : B.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  have : (sheafHom B (G.obj n)).IsQuasicoherent := isQuasicoherent_sheafHom B (G.obj n)
  have : (sheafHom B B).IsCoherent := isCoherent_sheafHom B B
  have : (sheafHom B B).IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  refine isIso_of_bijective_app_affine _ fun V hV ↦ ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨t, rfl⟩ := toQuotientIdealPow_app_surjective I f n hV (M := sheafHom B B) x
    rw [← Scheme.Modules.Hom.comp_app_apply, toQuotientIdealPow_algκbar] at hx
    have := hB hV
    rw [quotientIdealPow_app_eq_zero_iff I f _ n hV]
    exact mem_pow_smul_of_sheafHomPostcomp_app_eq_zero I f hV (algRed I f e n) (n + 1)
      (algRed_app_eq_zero I f e n hV) t hx
  · intro y
    have := hB hV
    obtain ⟨φ, hφ⟩ := Module.projective_lifting_property (appLinearMap (algRed I f e n) V)
      (sheafHomAffineEquiv hV B (G.obj n) y) (algRed_app_surjective I f e n hV)
    refine ⟨((sheafHom B B).toQuotientIdealPow f I n).app V
      ((sheafHomAffineEquiv hV B B).symm φ), ?_⟩
    rw [← Scheme.Modules.Hom.comp_app_apply, toQuotientIdealPow_algκbar]
    apply (sheafHomAffineEquiv hV B (G.obj n)).injective
    rw [sheafHomAffineEquiv_postcomp, LinearEquiv.apply_symm_apply, hφ]

end AlgebraizationMul

section AlgebraizationMain

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec A)

open Scheme.Modules

lemma sheafHomPostcomp_comp {M N N' N'' : X.Modules} (g : N ⟶ N') (g' : N' ⟶ N'') :
    sheafHomPostcomp (M := M) g ≫ sheafHomPostcomp g' = sheafHomPostcomp (g ≫ g') := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext φ
  exact HomOn.ext (funext fun V ↦ funext fun hV ↦ LinearMap.ext fun m ↦ rfl)

variable {B : X.Modules} {G : AdicSystem I f} (e : ∀ n, B.quotientIdealPow f I n ≅ G.obj n)
  (he : ∀ n, (e (n + 1)).hom ≫ G.map n = B.quotientIdealPowMap f I n ≫ (e n).hom)
  (alg : ∀ n, ModuleAlgebra (G.obj n))
  (hmul : ∀ (n : ℕ) (U : X.Opens) (x y : Γ(G.obj (n + 1), U)),
    (G.map n).app U (mulApp (alg (n + 1)).mul U x y) =
      mulApp (alg n).mul U ((G.map n).app U x) ((G.map n).app U y))
  (hone : ∀ n, (G.map n).app ⊤ (alg (n + 1)).one = (alg n).one)

omit [IsNoetherianRing A] in
include he hmul in
lemma algV_comp_map (n : ℕ) :
    algV I f e alg (n + 1) ≫ sheafHomPostcomp (G.map n) = algV I f e alg n := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext b
  refine HomOn.ext (funext fun V ↦ funext fun hV ↦ LinearMap.ext fun c ↦ ?_)
  change (G.map n).app V ((((algV I f e alg (n + 1)).app U b : Γ(sheafHom B _, U)) :
    HomOn B _ U).app V hV c) = (((algV I f e alg n).app U b : Γ(sheafHom B _, U)) :
      HomOn B _ U).app V hV c
  rw [algV_app, algV_app, hmul, ← Scheme.Modules.Hom.comp_app_apply,
    ← Scheme.Modules.Hom.comp_app_apply, algRed_comp I f e he]

variable [IsAdicComplete I A] [IsProper f]

include he hmul in
/-- **The multiplication algebraizes**: there is `μ : B ⟶ ℋom(B, B)` reducing to the
multiplications of the `Gₙ`. -/
theorem exists_mul_algebraization [B.IsCoherent]
    (hB : ∀ {V : X.Opens}, IsAffineOpen V → Module.Projective Γ(X, V) Γ(B, V)) :
    ∃ μ : B ⟶ sheafHom B B, ∀ n, μ ≫ algκ I f e n = algV I f e alg n := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : (sheafHom B B).IsCoherent := isCoherent_sheafHom B B
  have hiso := isIso_algκbar I f e hB
  let w : ∀ n, B ⟶ (sheafHom B B).quotientIdealPow f I n := fun n ↦
    algV I f e alg n ≫ inv (algκbar I f e n)
  have hA : ∀ n, (sheafHom B B).quotientIdealPowMap f I n ≫ algκbar I f e n =
      algκbar I f e (n + 1) ≫ sheafHomPostcomp (G.map n) := by
    intro n
    rw [← cancel_epi ((sheafHom B B).toQuotientIdealPow f I (n + 1)),
      Scheme.Modules.toQuotientIdealPow_comp_map_assoc, toQuotientIdealPow_algκbar,
      toQuotientIdealPow_algκbar_assoc, algκ, algκ, sheafHomPostcomp_comp, algRed_comp I f e he]
  have hw : ∀ n, w (n + 1) ≫ (sheafHom B B).quotientIdealPowMap f I n = w n := by
    intro n
    rw [← cancel_mono (algκbar I f e n)]
    simp only [w, Category.assoc, hA, IsIso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id]
    exact algV_comp_map I f e he alg hmul n
  obtain ⟨μ, hμ⟩ := exists_comp_toQuotientIdealPow_eq I f w hw
  refine ⟨μ, fun n ↦ ?_⟩
  rw [← toQuotientIdealPow_algκbar, ← Category.assoc, hμ, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id]

include he hone in
/-- **The unit algebraizes**. -/
theorem exists_one_algebraization [B.IsCoherent] :
    ∃ one : Γ(B, ⊤), ∀ n, (algRed I f e n).app ⊤ one = (alg n).one := by
  let z : ∀ n, Γ(B.quotientIdealPow f I n, ⊤) := fun n ↦ (e n).inv.app ⊤ (alg n).one
  have hz : ∀ n, (B.quotientIdealPowMap f I n).app ⊤ (z (n + 1)) = z n := by
    intro n
    have h1 : (e (n + 1)).inv ≫ B.quotientIdealPowMap f I n = G.map n ≫ (e n).inv := by
      rw [← cancel_mono (e n).hom, Category.assoc, Category.assoc, Iso.inv_hom_id,
        Category.comp_id, ← he, Iso.inv_hom_id_assoc]
    change ((e (n + 1)).inv ≫ B.quotientIdealPowMap f I n).app ⊤ (alg (n + 1)).one =
      (e n).inv.app ⊤ (alg n).one
    rw [h1, Scheme.Modules.Hom.comp_app_apply, hone]
  obtain ⟨one, hone', -⟩ := existsUnique_app_toQuotientIdealPow_eq I f B z hz
  refine ⟨one, fun n ↦ ?_⟩
  rw [algRed, Scheme.Modules.Hom.comp_app_apply, hone' n, ← Scheme.Modules.Hom.comp_app_apply,
    Iso.inv_hom_id]
  rfl

end AlgebraizationMain

section AlgebraizationAxioms

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec A)

open Scheme.Modules

variable {B : X.Modules} {G : AdicSystem I f} (e : ∀ n, B.quotientIdealPow f I n ≅ G.obj n)
  (alg : ∀ n, ModuleAlgebra (G.obj n)) {μ : B ⟶ sheafHom B B}
  (hμ : ∀ n, μ ≫ algκ I f e n = algV I f e alg n)

omit [IsNoetherianRing A] in
include hμ in
lemma algRed_mulApp (n : ℕ) (U : X.Opens) (x y : Γ(B, U)) :
    (algRed I f e n).app U (mulApp μ U x y) =
      mulApp (alg n).mul U ((algRed I f e n).app U x) ((algRed I f e n).app U y) := by
  have h := congrArg (fun φ : B ⟶ sheafHom B (G.obj n) ↦
    ((φ.app U x : Γ(sheafHom B (G.obj n), U)) : HomOn B (G.obj n) U).app U le_rfl y) (hμ n)
  simp only at h
  have h2 : (algRed I f e n).app U (mulApp μ U x y) =
      (((μ ≫ algκ I f e n).app U x : Γ(sheafHom B (G.obj n), U)) :
        HomOn B (G.obj n) U).app U le_rfl y := rfl
  rw [h2, h, algV_app, modules_map_self]

variable [IsAdicComplete I A] [IsProper f]

include hμ in
lemma mul_comm_algebraization [B.IsCoherent]
    (hB : ∀ {V : X.Opens}, IsAffineOpen V → Module.Projective Γ(X, V) Γ(B, V))
    (U : X.Opens) (x y : Γ(B, U)) : mulApp μ U x y = mulApp μ U y x := by
  have : B.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have key : μ = sheafHomEval B B ≫ sheafHomPrecomp μ := by
    refine eq_of_comp_sheafHomPostcomp_eq I f hB (algRed I f e)
      (fun n V hV x hx ↦ algRed_app_eq_zero I f e n hV x hx) fun n ↦ ?_
    refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
    ext b
    refine HomOn.ext (funext fun V ↦ funext fun hV ↦ LinearMap.ext fun c ↦ ?_)
    change (((μ ≫ algκ I f e n).app U b : Γ(sheafHom B (G.obj n), U)) :
      HomOn B (G.obj n) U).app V hV c = (algRed I f e n).app V (mulApp μ V c
        (B.presheaf.map (homOfLE hV).op b))
    rw [hμ n, algV_app, algRed_mulApp I f e alg hμ, (alg n).mul_comm]
  have h := congrArg (fun φ : B ⟶ sheafHom B B ↦
    ((φ.app U x : Γ(sheafHom B B, U)) : HomOn B B U).app U le_rfl y) key
  change mulApp μ U x y = mulApp μ U y (B.presheaf.map (homOfLE le_rfl).op x) at h
  rw [h, modules_map_self]

include hμ in
lemma mul_assoc_algebraization [B.IsCoherent]
    (hB : ∀ {V : X.Opens}, IsAffineOpen V → Module.Projective Γ(X, V) Γ(B, V))
    (U : X.Opens) (x y z : Γ(B, U)) :
    mulApp μ U (mulApp μ U x y) z = mulApp μ U x (mulApp μ U y z) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : B.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : (sheafHom B B).IsCoherent := isCoherent_sheafHom B B
  have key : μ ≫ sheafHomPostcomp μ = μ ≫ sheafHomComp B B B ≫ sheafHomPrecomp μ := by
    refine eq_of_comp_sheafHomPostcomp_eq I f hB (algκ I f e) (fun n V hV x hx ↦ ?_)
      fun n ↦ ?_
    · have := hB hV
      exact mem_pow_smul_of_sheafHomPostcomp_app_eq_zero I f hV (algRed I f e n) (n + 1)
        (algRed_app_eq_zero I f e n hV) x hx
    refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
    ext a
    refine HomOn.ext (funext fun V ↦ funext fun hV ↦ LinearMap.ext fun b ↦ ?_)
    refine HomOn.ext (funext fun W ↦ funext fun hW ↦ LinearMap.ext fun c ↦ ?_)
    change (algRed I f e n).app W ((((μ.app V (((μ.app U a : Γ(sheafHom B B, U)) :
        HomOn B B U).app V hV b)) : Γ(sheafHom B B, V)) : HomOn B B V).app W hW c) =
      (algRed I f e n).app W ((((μ.app U a : Γ(sheafHom B B, U)) : HomOn B B U)).app W
        (hW.trans hV) (((μ.app V b : Γ(sheafHom B B, V)) : HomOn B B V).app W hW c))
    rw [mulApp_eq μ hW, mulApp_eq μ hV, mulApp_res, mulApp_eq μ hW,
      mulApp_eq μ (hW.trans hV), algRed_mulApp I f e alg hμ,
      algRed_mulApp I f e alg hμ, algRed_mulApp I f e alg hμ, algRed_mulApp I f e alg hμ,
      (alg n).mul_assoc, modules_map_map_apply B (homOfLE hW) (homOfLE hV)
        (homOfLE (hW.trans hV))]
  have h := congrArg (fun φ : B ⟶ sheafHom B (sheafHom B B) ↦
    ((((φ.app U x : Γ(sheafHom B (sheafHom B B), U)) : HomOn B (sheafHom B B) U).app U le_rfl y :
      Γ(sheafHom B B, U)) : HomOn B B U).app U le_rfl z) key
  change mulApp μ U (mulApp μ U x y) z = mulApp μ U x (mulApp μ U y z) at h
  exact h

include hμ in
lemma one_mul_algebraization [B.IsCoherent] {one : Γ(B, ⊤)}
    (hone : ∀ n, (algRed I f e n).app ⊤ one = (alg n).one) (U : X.Opens) (x : Γ(B, U)) :
    mulApp μ U (B.presheaf.map (homOfLE le_top).op one) x = x := by
  have : B.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let φ₁ : B ⟶ B := homOnTopEquiv ((μ.app ⊤ one : Γ(sheafHom B B, ⊤)) : HomOn B B ⊤)
  have hφ₁ : ∀ (U : X.Opens) (x : Γ(B, U)),
      φ₁.app U x = mulApp μ U (B.presheaf.map (homOfLE le_top).op one) x := fun U x ↦
    homOn_app_res μ le_top one x
  have key : φ₁ = 𝟙 B := by
    refine eq_of_comp_toQuotientIdealPow_eq I f fun n ↦ ?_
    rw [← cancel_mono (e n).hom, Category.assoc, Category.id_comp]
    refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
    ext x
    change (algRed I f e n).app U (φ₁.app U x) = (algRed I f e n).app U x
    rw [hφ₁, algRed_mulApp I f e alg hμ, hom_app_presheaf_map, hone, (alg n).one_mul]
  have := congrArg (fun φ : B ⟶ B ↦ φ.app U x) key
  simp only at this
  rw [← hφ₁, this]
  rfl

include hμ in
/-- **Algebraization of algebra structures** (EGA III 5.4.1 for finite algebras): let `A` be
noetherian and `I`-adically complete, `X` proper over `Spec A`, `B` coherent with projective
sections over affine opens and compatible isomorphisms `B / I^{n+1} B ≅ Gₙ`. Compatible commutative
algebra structures on the `Gₙ` come from a unique (by construction, reducing to them) commutative
algebra structure on `B`. -/
theorem exists_moduleAlgebra_algebraization [B.IsCoherent]
    (hB : ∀ {V : X.Opens}, IsAffineOpen V → Module.Projective Γ(X, V) Γ(B, V))
    {one : Γ(B, ⊤)} (hone : ∀ n, (algRed I f e n).app ⊤ one = (alg n).one) :
    ∃ algB : ModuleAlgebra B, algB.mul = μ ∧ algB.one = one :=
  ⟨{ mul := μ
     one := one
     mul_comm := mul_comm_algebraization I f e alg hμ hB
     mul_assoc := mul_assoc_algebraization I f e alg hμ hB
     one_mul := one_mul_algebraization I f e alg hμ hone }, rfl, rfl⟩

end AlgebraizationAxioms

end AlgebraicGeometry.CohomologyAux
