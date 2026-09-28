/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.FormalFunctions

/-!
# Separating global functions on proper schemes

The step of Zariski's connectedness theorem (EGA III 4.3.1; Hartshorne III.11.3) which uses the
theorem on formal functions: for `A` noetherian, `f : X ⟶ Spec A` proper and `I ⊆ A`, a
decomposition of `f⁻¹ V(I)` into two disjoint closed pieces `G₁, G₂` gives a global function
`a ∈ Γ(X, 𝒪_X)` equal to `1` near `G₁` and to `0` near `G₂` modulo `I`
(`CohomologyAux.exists_section_separating`). The idempotents `1_{G₁}` of `Γ(X, 𝒪_X / I^{n+1})`
(glued with `exists_glue₂`, since `𝒪_X / I^{n+1}` vanishes off `f⁻¹ V(I)`,
`quotientIdealPow_app_eq_zero`) form an element of `lim_n H⁰(X, 𝒪_X / I^{n+1})`, which lifts to
`H⁰(X, 𝒪_X)` by `exists_H'_map_toQuotientIdealPow_eq`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.CohomologyAux

section Sections

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec A) (M : X.Modules) [M.IsQuasicoherent]

omit [M.IsQuasicoherent] in
set_option maxRecDepth 10000 in
/-- Exactness of `Γ(U, I^{n+1} M) → Γ(U, M) → Γ(U, M / I^{n+1} M)`. -/
lemma toQuotientIdealPow_app_eq_zero_iff (n : ℕ) (U : X.Opens) (s : Γ(M, U)) :
    (M.toQuotientIdealPow f I n).app U s = 0 ↔ s ∈ Set.range ((ιPow f I M (n + 1)).app U) := by
  let x := (CategoryTheory.Sheaf.H'.equiv₀ M.toAbSheaf U).symm s
  have hex : Scheme.Modules.H'.map (M.toQuotientIdealPow f I n) 0 U x = 0 ↔
      x ∈ Set.range (Scheme.Modules.H'.map (ιPow f I M (n + 1)) 0 U) :=
    Scheme.Modules.H'.exact_map_map (shortExact_quotientIdealPow f I M n) 0 U x
  have e₁ : Scheme.Modules.H'.map (M.toQuotientIdealPow f I n) 0 U x =
      (CategoryTheory.Sheaf.H'.equiv₀ _ U).symm ((M.toQuotientIdealPow f I n).app U s) :=
    CategoryTheory.Sheaf.H'.equiv₀_symm_naturality
      (Scheme.Modules.Hom.toAbSheaf (M.toQuotientIdealPow f I n)) (U := U) s
  have h0 : (M.toQuotientIdealPow f I n).app U s = 0 ↔
      Scheme.Modules.H'.map (M.toQuotientIdealPow f I n) 0 U x = 0 := by
    rw [e₁]
    exact (AddEquiv.map_eq_zero_iff _).symm
  refine h0.trans (hex.trans ?_)
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨CategoryTheory.Sheaf.H'.equiv₀ _ U y, ?_⟩
    have e₂ : CategoryTheory.Sheaf.H'.equiv₀ M.toAbSheaf U
        (Scheme.Modules.H'.map (ιPow f I M (n + 1)) 0 U y) =
        (ιPow f I M (n + 1)).app U (CategoryTheory.Sheaf.H'.equiv₀ _ U y) :=
      CategoryTheory.Sheaf.H'.equiv₀_naturality
        (Scheme.Modules.Hom.toAbSheaf (ιPow f I M (n + 1))) (U := U) y
    rw [← e₂, hy]
    exact AddEquiv.apply_symm_apply _ _
  · rintro ⟨t, rfl⟩
    refine ⟨(CategoryTheory.Sheaf.H'.equiv₀ _ U).symm t, ?_⟩
    exact CategoryTheory.Sheaf.H'.equiv₀_symm_naturality
      (Scheme.Modules.Hom.toAbSheaf (ιPow f I M (n + 1))) (U := U) t

variable {M} in
/-- On an affine open, `Γ(U, M) → Γ(U, M / I^{n+1} M)` is surjective. -/
lemma toQuotientIdealPow_app_surjective (n : ℕ) {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Surjective ((M.toQuotientIdealPow f I n).app U) := by
  have := isQuasicoherent_IPow I f M (n + 1)
  exact TopCat.Sheaf.surjective_app_of_subsingleton_H'_one
    (Scheme.Modules.shortExact_abShortComplex (shortExact_quotientIdealPow f I M n)) U
    ((IPow f I M (n + 1)).H'_subsingleton_of_isAffineOpen hU 0)

end Sections

section Separate

variable {X : Scheme.{u}}

/-- Two sections of an `𝒪_X`-module agreeing on all affine opens are equal. -/
lemma section_ext_affine {N : X.Modules} {U : X.Opens} {s t : Γ(N, U)}
    (h : ∀ (V : X.Opens) (_ : IsAffineOpen V) (hVU : V ≤ U),
      N.presheaf.map (homOfLE hVU).op s = N.presheaf.map (homOfLE hVU).op t) : s = t := by
  apply N.isSheaf.section_ext (U := op U)
  intro x hx
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  exact ⟨V, hVU, hxV, h V hV hVU⟩

/-- The ideal of sections over `U` vanishing at `x ∈ U`. -/
noncomputable def pointIdeal {U : X.Opens} {x : X} (hx : x ∈ U) : Ideal Γ(X, U) :=
  (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.germ U x hx).hom

lemma mem_pointIdeal {U : X.Opens} {x : X} (hx : x ∈ U) (s : Γ(X, U)) :
    s ∈ pointIdeal hx ↔ x ∉ X.basicOpen s := by
  rw [pointIdeal, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Scheme.mem_basicOpen X s x hx]

variable {A : CommRingCat.{u}} (I : Ideal A) (f : X ⟶ Spec A)

/-- The closed subset `f⁻¹ V(I) ⊆ X`, as the common zero locus of the `a ∈ I`. -/
def zeroLocusPreimage : Set X := {x | ∀ a ∈ I, x ∉ X.basicOpen (f.specStructureRingHom a)}

lemma isClosed_zeroLocusPreimage : IsClosed (zeroLocusPreimage I f) := by
  have : zeroLocusPreimage I f =
      ⋂ a ∈ I, ((X.basicOpen (f.specStructureRingHom a) : X.Opens) : Set X)ᶜ := by
    ext x
    simp [zeroLocusPreimage]
  rw [this]
  exact isClosed_biInter fun a _ ↦ (X.basicOpen _).isOpen.isClosed_compl

lemma structMapV_eq_map (U : X.Opens) (a : A) :
    structMapV f U a = X.presheaf.map (homOfLE le_top).op (f.specStructureRingHom a) := rfl

/-- `Iⁿ 𝒪(U) = 𝒪(U)` on an affine open `U` disjoint from `f⁻¹ V(I)`. -/
lemma idealV_eq_top {U : X.Opens} (hU : IsAffineOpen U)
    (hUW : ∀ x ∈ U, x ∉ zeroLocusPreimage I f) (n : ℕ) : idealV f I U n = ⊤ := by
  have h1 : idealV f I U 1 = ⊤ := by
    rw [idealV, pow_one, eq_top_iff]
    rw [← (hU.self_le_iSup_basicOpen_iff (s := structMapV f U '' I)).mp ?_]
    · exact Ideal.span_le.mpr (by rintro _ ⟨a, ha, rfl⟩; exact Ideal.mem_map_of_mem _ ha)
    · intro x hx
      obtain ⟨a, ha, hxa⟩ : ∃ a ∈ I, x ∈ X.basicOpen (f.specStructureRingHom a) := by
        by_contra h
        push Not at h
        exact hUW x hx h
      refine Opens.mem_iSup.mpr ⟨⟨structMapV f U a, a, ha, rfl⟩, ?_⟩
      change x ∈ X.basicOpen (structMapV f U a)
      rw [structMapV_eq_map, Scheme.basicOpen_res]
      exact ⟨hx, hxa⟩
  have : idealV f I U n = idealV f I U 1 ^ n := by rw [idealV, idealV, pow_one, Ideal.map_pow]
  rw [this, h1, Ideal.top_pow]

variable [IsNoetherianRing A] (M : X.Modules) [M.IsQuasicoherent]

/-- `M / I^{n+1} M` vanishes off `f⁻¹ V(I)`. -/
lemma quotientIdealPow_app_eq_zero {U : X.Opens} (hUW : ∀ x ∈ U, x ∉ zeroLocusPreimage I f)
    (n : ℕ) (t : Γ(M.quotientIdealPow f I n, U)) : t = 0 := by
  refine section_ext_affine fun V hV hVU ↦ ?_
  rw [map_zero]
  obtain ⟨s, hs⟩ := toQuotientIdealPow_app_surjective I f n hV
    ((M.quotientIdealPow f I n).presheaf.map (homOfLE hVU).op t)
  rw [← hs, toQuotientIdealPow_app_eq_zero_iff]
  refine (mem_range_ιPow_app f I M hV (n + 1) s).mpr ?_
  rw [idealV_eq_top I f hV (fun x hx ↦ hUW x (hVU hx)), Submodule.top_smul]
  exact Submodule.mem_top

end Separate

section Glue

variable {X : Scheme.{u}}

/-- Gluing two sections of an `𝒪_X`-module over an open cover `X = U₁ ∪ U₂`. -/
lemma exists_glue₂ (N : X.Modules) {U₁ U₂ : X.Opens} (hcov : ⊤ ≤ U₁ ⊔ U₂) (s₁ : Γ(N, U₁))
    (s₂ : Γ(N, U₂))
    (h : N.presheaf.map (homOfLE inf_le_left : U₁ ⊓ U₂ ⟶ U₁).op s₁ =
      N.presheaf.map (homOfLE inf_le_right : U₁ ⊓ U₂ ⟶ U₂).op s₂) :
    ∃ s : Γ(N, ⊤), N.presheaf.map (homOfLE le_top : U₁ ⟶ ⊤).op s = s₁ ∧
      N.presheaf.map (homOfLE le_top : U₂ ⟶ ⊤).op s = s₂ := by
  have key : ∀ (V : X.Opens) (hV₁ : V ≤ U₁) (hV₂ : V ≤ U₂),
      N.presheaf.map (homOfLE hV₁).op s₁ = N.presheaf.map (homOfLE hV₂).op s₂ := by
    intro V hV₁ hV₂
    have e₁ : (homOfLE hV₁).op = (homOfLE inf_le_left : U₁ ⊓ U₂ ⟶ U₁).op ≫
        (homOfLE (le_inf hV₁ hV₂)).op := rfl
    have e₂ : (homOfLE hV₂).op = (homOfLE inf_le_right : U₁ ⊓ U₂ ⟶ U₂).op ≫
        (homOfLE (le_inf hV₁ hV₂)).op := rfl
    rw [e₁, e₂, Functor.map_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, h]
  let U : Bool → X.Opens := fun b ↦ cond b U₁ U₂
  let sf : ∀ b, Γ(N, U b) := fun b ↦ Bool.rec (motive := fun b ↦ Γ(N, U b)) s₂ s₁ b
  have hc : TopCat.Presheaf.IsCompatible N.toAbSheaf.1 U sf := by
    rintro (_ | _) (_ | _)
    · rfl
    · exact (key _ inf_le_right inf_le_left).symm
    · exact key _ inf_le_left inf_le_right
    · rfl
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' N.toAbSheaf U ⊤
    (fun _ ↦ homOfLE le_top) (by
      refine hcov.trans (sup_le ?_ ?_)
      · exact le_iSup U true
      · exact le_iSup U false) sf hc
  exact ⟨t, ht true, ht false⟩

end Glue

section Main

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec A)

omit [IsNoetherianRing A] in
lemma idealV_le_pointIdeal {V : X.Opens} {x : X} (hxV : x ∈ V) (hxW : x ∈ zeroLocusPreimage I f) :
    idealV f I V 1 ≤ pointIdeal hxV := by
  rw [idealV, pow_one, Ideal.map_le_iff_le_comap]
  intro b hb
  rw [Ideal.mem_comap, mem_pointIdeal, structMapV_eq_map, Scheme.basicOpen_res]
  exact fun h ↦ hxW b hb h.2

omit [IsNoetherianRing A] in
lemma mem_idealV_of_mem_smul_top {V : X.Opens} (s : Γ(unitModule X, V))
    (hs : s ∈ idealV f I V 1 • (⊤ : Submodule Γ(X, V) Γ(unitModule X, V))) :
    @id Γ(X, V) s ∈ idealV f I V 1 := by
  refine Submodule.smul_induction_on hs (fun r hr m _ ↦ ?_) (fun m m' hm hm' ↦ ?_)
  · exact Ideal.mul_mem_right _ _ hr
  · exact Ideal.add_mem _ hm hm'

variable {G₁ G₂ : Set X} (hG₁ : IsClosed G₁) (hG₂ : IsClosed G₂)

/-- The open `X \ G₂`, on which the separating functions are `1`. -/
def sepOpen₁ : X.Opens := ⟨G₂ᶜ, hG₂.isOpen_compl⟩

/-- The open `X \ (G₁ ∩ f⁻¹ V(I))`, on which the separating functions are `0`. -/
def sepOpen₂ : X.Opens := ⟨(G₁ ∩ zeroLocusPreimage I f)ᶜ,
  (hG₁.inter (isClosed_zeroLocusPreimage I f)).isOpen_compl⟩

variable {I f} (hcov : zeroLocusPreimage I f ⊆ G₁ ∪ G₂)
  (hdisj : ∀ x ∈ zeroLocusPreimage I f, x ∈ G₁ → x ∉ G₂)

omit [IsNoetherianRing A] in
include hdisj in
lemma sepOpen_cover : ⊤ ≤ sepOpen₁ hG₂ ⊔ sepOpen₂ I f hG₁ := by
  intro x _
  rw [Opens.mem_sup]
  by_cases hx : x ∈ G₂
  · exact Or.inr fun hx' ↦ hdisj x hx'.2 hx'.1 hx
  · exact Or.inl hx

omit [IsNoetherianRing A] in
include hcov in
lemma sepOpen_inter : ∀ x ∈ sepOpen₁ hG₂ ⊓ sepOpen₂ I f hG₁, x ∉ zeroLocusPreimage I f := by
  rintro x ⟨hx₁, hx₂⟩ hxW
  rcases hcov hxW with h | h
  · exact hx₂ ⟨h, hxW⟩
  · exact hx₁ h

include hcov hdisj in
variable (I f) in
/-- The compatible idempotent sections `1_{G₁}` of `𝒪_X / I^{n+1}` (equal to `1` off `G₂` and to `0`
off `G₁ ∩ f⁻¹ V(I)`). -/
lemma exists_separatingFamily :
    ∃ z : ∀ n, Γ((unitModule X).quotientIdealPow f I n, ⊤),
      (∀ n, ((unitModule X).quotientIdealPowMap f I n).app ⊤ (z (n + 1)) = z n) ∧
      (∀ n, ((unitModule X).quotientIdealPow f I n).presheaf.map
        (homOfLE le_top : sepOpen₁ hG₂ ⟶ ⊤).op (z n) =
          ((unitModule X).toQuotientIdealPow f I n).app (sepOpen₁ hG₂)
            (1 : Γ(X, sepOpen₁ hG₂))) ∧
      (∀ n, ((unitModule X).quotientIdealPow f I n).presheaf.map
        (homOfLE le_top : sepOpen₂ I f hG₁ ⟶ ⊤).op (z n) = 0) := by
  let O := unitModule X
  let U₁ := sepOpen₁ hG₂
  let U₂ := sepOpen₂ I f hG₁
  have hcov' : ⊤ ≤ U₁ ⊔ U₂ := sepOpen_cover hG₁ hG₂ hdisj
  have hU₁₂ : ∀ x ∈ U₁ ⊓ U₂, x ∉ zeroLocusPreimage I f := sepOpen_inter hG₁ hG₂ hcov
  have hglue : ∀ n, ∃ z : Γ(O.quotientIdealPow f I n, ⊤),
      (O.quotientIdealPow f I n).presheaf.map (homOfLE le_top : U₁ ⟶ ⊤).op z =
        (O.toQuotientIdealPow f I n).app U₁ (1 : Γ(X, U₁)) ∧
      (O.quotientIdealPow f I n).presheaf.map (homOfLE le_top : U₂ ⟶ ⊤).op z = 0 := fun n ↦
    exists_glue₂ _ hcov' _ _ ((quotientIdealPow_app_eq_zero I f O hU₁₂ n _).trans
      (quotientIdealPow_app_eq_zero I f O hU₁₂ n _).symm)
  choose z hz₁ hz₂ using hglue
  refine ⟨z, fun n ↦ ?_, hz₁, hz₂⟩
  refine TopCat.Sheaf.eq_of_locally_eq₂ (O.quotientIdealPow f I n).toAbSheaf
    (homOfLE le_top : U₁ ⟶ ⊤) (homOfLE le_top : U₂ ⟶ ⊤) hcov' _ _ ?_ ?_
  · change (O.quotientIdealPow f I n).presheaf.map _
        ((O.quotientIdealPowMap f I n).app ⊤ (z (n + 1))) =
      (O.quotientIdealPow f I n).presheaf.map _ (z n)
    have hcomp : ∀ t : Γ(O, U₁), (O.quotientIdealPowMap f I n).app U₁
        ((O.toQuotientIdealPow f I (n + 1)).app U₁ t) = (O.toQuotientIdealPow f I n).app U₁ t :=
      fun t ↦ by rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
        Scheme.Modules.toQuotientIdealPow_comp_map]
    rw [← hom_app_presheaf_map, hz₁, hz₁]
    exact hcomp _
  · change (O.quotientIdealPow f I n).presheaf.map _
        ((O.quotientIdealPowMap f I n).app ⊤ (z (n + 1))) =
      (O.quotientIdealPow f I n).presheaf.map _ (z n)
    rw [← hom_app_presheaf_map, hz₂, hz₂, map_zero]

include hdisj in
/-- A global function `a` reducing to the idempotent `1_{G₁}` of `𝒪_X / I` is invertible on
`G₁ ∩ f⁻¹ V(I)` and vanishes on `G₂ ∩ f⁻¹ V(I)`. -/
lemma separating_of_toQuotientIdealPow_eq (z : Γ((unitModule X).quotientIdealPow f I 0, ⊤))
    (hz₁ : ((unitModule X).quotientIdealPow f I 0).presheaf.map
        (homOfLE le_top : sepOpen₁ hG₂ ⟶ ⊤).op z =
          ((unitModule X).toQuotientIdealPow f I 0).app (sepOpen₁ hG₂)
            (1 : Γ(X, sepOpen₁ hG₂)))
    (hz₂ : ((unitModule X).quotientIdealPow f I 0).presheaf.map
        (homOfLE le_top : sepOpen₂ I f hG₁ ⟶ ⊤).op z = 0)
    (a : Γ(X, ⊤)) (ha : ((unitModule X).toQuotientIdealPow f I 0).app ⊤ a = z) :
    (∀ x ∈ zeroLocusPreimage I f, x ∈ G₁ → x ∈ X.basicOpen a) ∧
      (∀ x ∈ zeroLocusPreimage I f, x ∈ G₂ → x ∉ X.basicOpen a) := by
  set W := zeroLocusPreimage I f
  let O := unitModule X
  let U₁ := sepOpen₁ hG₂
  let U₂ := sepOpen₂ I f hG₁
  have hres : ∀ (V : X.Opens), (O.toQuotientIdealPow f I 0).app V
      (O.presheaf.map (homOfLE le_top : V ⟶ ⊤).op a) =
      (O.quotientIdealPow f I 0).presheaf.map (homOfLE le_top : V ⟶ ⊤).op z := fun V ↦
    (hom_app_presheaf_map (O.toQuotientIdealPow f I 0) (homOfLE le_top : V ⟶ ⊤)
      (show Γ(O, ⊤) from a)).trans (congrArg _ ha)
  have hmem : ∀ (V : X.Opens) (hV : IsAffineOpen V) (x : X) (hxV : x ∈ V) (hxW : x ∈ W)
      (t : Γ(O, V)), (O.toQuotientIdealPow f I 0).app V t = 0 →
        @id Γ(X, V) t ∈ pointIdeal hxV := by
    intro V hV x hxV hxW t ht
    rw [toQuotientIdealPow_app_eq_zero_iff, mem_range_ιPow_app f I O hV] at ht
    exact idealV_le_pointIdeal I f hxV hxW (mem_idealV_of_mem_smul_top I f t ht)
  have hbo : ∀ (V : X.Opens) (x : X) (hxV : x ∈ V),
      @id Γ(X, V) (O.presheaf.map (homOfLE le_top : V ⟶ ⊤).op a) ∈ pointIdeal hxV ↔
        x ∉ X.basicOpen a := by
    intro V x hxV
    rw [mem_pointIdeal]
    change x ∉ X.basicOpen (X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op a) ↔ _
    rw [Scheme.basicOpen_res]
    exact ⟨fun h h' ↦ h ⟨hxV, h'⟩, fun h h' ↦ h h'.2⟩
  refine ⟨fun x hxW hx₁ ↦ ?_, fun x hxW hx₂ ↦ ?_⟩
  · have hxU₁ : x ∈ U₁ := hdisj x hxW hx₁
    obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxU₁
    let t : Γ(O, V) := O.presheaf.map (homOfLE le_top : V ⟶ ⊤).op a
    let one : Γ(O, V) := (1 : Γ(X, V))
    have hone : (O.toQuotientIdealPow f I 0).app V one =
        (O.quotientIdealPow f I 0).presheaf.map (homOfLE le_top : V ⟶ ⊤).op z := by
      have e : (homOfLE le_top : V ⟶ ⊤).op = (homOfLE le_top : U₁ ⟶ ⊤).op ≫ (homOfLE hVU).op :=
        rfl
      rw [e, Functor.map_comp, ConcreteCategory.comp_apply, hz₁]
      refine Eq.trans ?_ (hom_app_presheaf_map (O.toQuotientIdealPow f I 0) (homOfLE hVU)
        (show Γ(O, U₁) from (1 : Γ(X, U₁))))
      congr 1
      exact (map_one (X.presheaf.map (homOfLE hVU).op).hom).symm
    have h0 : (O.toQuotientIdealPow f I 0).app V (one - t) = 0 := by
      rw [map_sub, hone, hres, sub_self]
    have h1 : @id Γ(X, V) (one - t) ∈ pointIdeal hxV := hmem V hV x hxV hxW _ h0
    by_contra hxa
    have h2 : @id Γ(X, V) t ∈ pointIdeal hxV := (hbo V x hxV).mpr hxa
    have h3 : (1 : Γ(X, V)) ∈ pointIdeal hxV := by
      have e : (1 : Γ(X, V)) = @id Γ(X, V) (one - t) + @id Γ(X, V) t :=
        (sub_add_cancel one t).symm
      rw [e]
      exact Ideal.add_mem _ h1 h2
    rw [mem_pointIdeal, Scheme.basicOpen_one] at h3
    exact h3 hxV
  · have hxU₂ : x ∈ U₂ := fun h ↦ hdisj x hxW h.1 hx₂
    obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxU₂
    have h0 : (O.toQuotientIdealPow f I 0).app V
        (O.presheaf.map (homOfLE le_top : V ⟶ ⊤).op a) = 0 := by
      rw [hres]
      have e : (homOfLE le_top : V ⟶ ⊤).op = (homOfLE le_top : U₂ ⟶ ⊤).op ≫ (homOfLE hVU).op :=
        rfl
      rw [e, Functor.map_comp, ConcreteCategory.comp_apply, hz₂, map_zero]
    exact (hbo V x hxV).mp (hmem V hV x hxV hxW _ h0)

omit [IsNoetherianRing A] in
/-- The family `z` as an element of `lim_n H⁰(X, 𝒪_X / I^{n+1})`. -/
lemma mem_formalLimit_of_compat (z : ∀ n, Γ((unitModule X).quotientIdealPow f I n, ⊤))
    (hcompat : ∀ n, ((unitModule X).quotientIdealPowMap f I n).app ⊤ (z (n + 1)) = z n) :
    (fun n ↦ (Scheme.Modules.H.equiv₀ _).symm (z n)) ∈ (unitModule X).formalLimit f I 0 := by
  intro n
  apply (Scheme.Modules.H.equiv₀ ((unitModule X).quotientIdealPow f I n)).injective
  have e := CategoryTheory.Sheaf.H'.equiv₀_symm_naturality
    (Scheme.Modules.Hom.toAbSheaf ((unitModule X).quotientIdealPowMap f I n)) (U := ⊤)
    (z (n + 1))
  refine (congrArg (Scheme.Modules.H.equiv₀ ((unitModule X).quotientIdealPow f I n)) e).trans ?_
  refine ((Scheme.Modules.H.equiv₀ _).apply_symm_apply _).trans ?_
  refine (hcompat n).trans ?_
  exact ((Scheme.Modules.H.equiv₀ _).apply_symm_apply _).symm

omit [IsNoetherianRing A] in
/-- `H⁰` and `Γ` for the reduction maps. -/
lemma equiv₀_H'_map_toQuotientIdealPow (n : ℕ) (y : (unitModule X).H 0) :
    Scheme.Modules.H.equiv₀ _ (Scheme.Modules.H'.map
      ((unitModule X).toQuotientIdealPow f I n) 0 ⊤ y) =
      ((unitModule X).toQuotientIdealPow f I n).app ⊤ (Scheme.Modules.H.equiv₀ _ y) :=
  CategoryTheory.Sheaf.H'.equiv₀_naturality
    (Scheme.Modules.Hom.toAbSheaf ((unitModule X).toQuotientIdealPow f I n)) (U := ⊤) y

variable [IsProper f]

variable (I f) in
/-- **Separating global functions** (EGA III 4.3.1, proof). Let `A` be noetherian, `f : X ⟶ Spec A`
proper and `I ⊆ A` an ideal, and suppose `f⁻¹ V(I) ⊆ G₁ ∪ G₂` for closed `G₁, G₂ ⊆ X` which are
disjoint on `f⁻¹ V(I)`. Then there is `a ∈ Γ(X, 𝒪_X)` which is invertible at the points of
`G₁ ∩ f⁻¹ V(I)` and vanishes at the points of `G₂ ∩ f⁻¹ V(I)`. It is obtained by lifting the
idempotents `1_{G₁}` of `Γ(X, 𝒪_X / I^{n+1})` along the theorem on formal functions (only the
existence of lifts, `exists_H'_map_toQuotientIdealPow_eq`, is needed). -/
theorem exists_section_separating (G₁ G₂ : Set X) (hG₁ : IsClosed G₁) (hG₂ : IsClosed G₂)
    (hcov : zeroLocusPreimage I f ⊆ G₁ ∪ G₂)
    (hdisj : ∀ x ∈ zeroLocusPreimage I f, x ∈ G₁ → x ∉ G₂) :
    ∃ a : Γ(X, ⊤), (∀ x ∈ zeroLocusPreimage I f, x ∈ G₁ → x ∈ X.basicOpen a) ∧
      (∀ x ∈ zeroLocusPreimage I f, x ∈ G₂ → x ∉ X.basicOpen a) := by
  obtain ⟨z, hcompat, hz₁, hz₂⟩ := exists_separatingFamily I f hG₁ hG₂ hcov hdisj
  have : (unitModule X).IsCoherent := isCoherent_unitModule X
  obtain ⟨y, hy⟩ := exists_H'_map_toQuotientIdealPow_eq I f (unitModule X) 0
    ⟨_, mem_formalLimit_of_compat z hcompat⟩ 0
  let a : Γ(X, ⊤) := Scheme.Modules.H.equiv₀ _ y
  have ha : ((unitModule X).toQuotientIdealPow f I 0).app ⊤ a = z 0 := by
    rw [← equiv₀_H'_map_toQuotientIdealPow, hy]
    exact (Scheme.Modules.H.equiv₀ _).apply_symm_apply _
  exact ⟨a, separating_of_toQuotientIdealPow_eq hG₁ hG₂ hdisj (z 0) (hz₁ 0) (hz₂ 0) a ha⟩

end Main

end AlgebraicGeometry.CohomologyAux
