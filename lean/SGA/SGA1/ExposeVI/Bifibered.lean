/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.Cofibered
import SGA.SGA1.ExposeVI.Cleavage
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# SGA 1, Exposé VI, §10: direct images, adjunctions, VI.10.1

For `f : T ⟶ S`, a direct image functor `f_* : 𝒳_T ⥤ 𝒳_S` (cocartesian transports) and an
inverse image functor `f^* : 𝒳_S ⥤ 𝒳_T` (cartesian transports) are adjoint,
`Hom_S(f_* η, ξ) ≃ Hom_f(η, ξ) ≃ Hom_T(η, f^* ξ)`; conversely, if `f_*` exists, every right
adjoint of `f_*` is an inverse image functor. For composable `f, g` the comparisons
`c^{f,g} : (fg)_* ⟶ f_* g_*` and `c_{f,g} : g^* f^* ⟶ (fg)^*` are conjugate (mates) under these
adjunctions, so one is an isomorphism iff the other is. VI.10.1: a prefibered and
coprefibered category is fibered iff it is cofibered.
-/

universe v₁ v₂ u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u₁} {C : Type u₂} [Category.{v₁} E] [Category.{v₂} C] {p : C ⥤ E}

/-- VI.5.1: an inverse image functor for one arrow `f : T ⟶ S`. -/
structure InverseImage (p : C ⥤ E) {T S : E} (f : T ⟶ S) where
  functor : Fiber p S ⥤ Fiber p T
  transport (ξ : Fiber p S) : (functor.obj ξ).val ⟶ ξ.val
  isCartesian (ξ : Fiber p S) : IsCartesian p f (transport ξ)
  natural {ξ ξ' : Fiber p S} (u : ξ ⟶ ξ') :
    (functor.map u).val ≫ transport ξ' = transport ξ ≫ u.val

/-- VI.10: a direct image functor for one arrow `f : T ⟶ S`. -/
structure DirectImage (p : C ⥤ E) {T S : E} (f : T ⟶ S) where
  functor : Fiber p T ⥤ Fiber p S
  transport (η : Fiber p T) : η.val ⟶ (functor.obj η).val
  isCocartesian (η : Fiber p T) : IsCocartesian p f (transport η)
  natural {η η' : Fiber p T} (u : η ⟶ η') :
    transport η ≫ (functor.map u).val = u.val ≫ transport η'

attribute [instance] InverseImage.isCartesian DirectImage.isCocartesian

/-- The inverse image functor for `f` given by a cleavage. -/
def Cleavage.inverseImage (K : Cleavage p) {T S : E} (f : T ⟶ S) : InverseImage p f where
  functor := K.pullback f
  transport := K.transport f
  isCartesian := K.transport_isCartesian f
  natural := K.transport_natural f

namespace DirectImage

variable {T S : E} {f : T ⟶ S} (D : DirectImage p f)

@[reassoc]
theorem natural' {η η' : Fiber p T} (u : η ⟶ η') :
    D.transport η ≫ (D.functor.map u).val = u.val ≫ D.transport η' :=
  D.natural u

variable (I : InverseImage p f)

/-- VI.10: `Hom_S(f_* η, ξ) ≃ Hom_f(η, ξ) ≃ Hom_T(η, f^* ξ)`. -/
noncomputable def homEquiv (η : Fiber p T) (ξ : Fiber p S) :
    (D.functor.obj η ⟶ ξ) ≃ (η ⟶ I.functor.obj ξ) where
  toFun u := ⟨IsCartesian.map p f (I.transport ξ) (D.transport η ≫ u.val), inferInstance⟩
  invFun v := ⟨IsCocartesian.map p f (D.transport η) (v.val ≫ I.transport ξ), inferInstance⟩
  left_inv u := Subtype.ext (IsCocartesian.map_uniq p f _ _ _ (by simp)).symm
  right_inv v := Subtype.ext (IsCartesian.map_uniq p f _ _ _ (by simp)).symm

@[reassoc (attr := simp)]
theorem homEquiv_fac {η : Fiber p T} {ξ : Fiber p S} (u : D.functor.obj η ⟶ ξ) :
    (D.homEquiv I η ξ u).val ≫ I.transport ξ = D.transport η ≫ u.val :=
  IsCartesian.fac p f _ _

@[reassoc (attr := simp)]
theorem homEquiv_symm_fac {η : Fiber p T} {ξ : Fiber p S} (v : η ⟶ I.functor.obj ξ) :
    D.transport η ≫ ((D.homEquiv I η ξ).symm v).val = v.val ≫ I.transport ξ :=
  IsCocartesian.fac p f _ _

/-- VI.10: the direct image functor is left adjoint to the inverse image functor. -/
noncomputable def adjunction : D.functor ⊣ I.functor :=
  Adjunction.mkOfHomEquiv
    { homEquiv := D.homEquiv I
      homEquiv_naturality_left_symm := fun {η' η ξ} w v ↦ Subtype.ext <| by
        apply IsCocartesian.ext p f (D.transport η')
        simp [D.natural'_assoc]
      homEquiv_naturality_right := fun {η ξ ξ'} u w ↦ Subtype.ext <| by
        apply IsCartesian.ext p f (I.transport ξ')
        simp [I.natural] }

/-- The counit of `f_* ⊣ f^*` composed with the cocartesian transport is the cartesian
transport. -/
@[reassoc (attr := simp)]
theorem transport_counit (ξ : Fiber p S) :
    D.transport (I.functor.obj ξ) ≫ ((D.adjunction I).counit.app ξ).val = I.transport ξ := by
  have : (D.adjunction I).counit.app ξ = (D.homEquiv I _ ξ).symm (𝟙 _) := rfl
  rw [this, homEquiv_symm_fac]
  simp

/-- VI.10: if the direct image functor `f_*` exists, any right adjoint of `f_*` is an inverse
image functor for `f`: the transport is `f_* f^* ξ ⟶ ξ` precomposed with `f^*ξ ⟶ f_* f^* ξ`. -/
noncomputable def inverseImageOfAdjunction {G : Fiber p S ⥤ Fiber p T}
    (adj : D.functor ⊣ G) : InverseImage p f where
  functor := G
  transport ξ := D.transport (G.obj ξ) ≫ (adj.counit.app ξ).val
  isCartesian ξ := by
    refine ⟨fun {a'} φ hφ ↦ ?_⟩
    let η : Fiber p T := ⟨a', IsHomLift.domain_eq p f φ⟩
    let φ' : D.functor.obj η ⟶ ξ := ⟨IsCocartesian.map p f (D.transport η) φ, inferInstance⟩
    have key : ∀ χ : η ⟶ G.obj ξ, χ.val ≫ D.transport (G.obj ξ) ≫ (adj.counit.app ξ).val =
        D.transport η ≫ ((adj.homEquiv η ξ).symm χ).val := by
      intro χ
      rw [Adjunction.homEquiv_counit, fiber_comp_val, D.natural'_assoc]
    refine ⟨(adj.homEquiv η ξ φ').val, ⟨inferInstance, ?_⟩, ?_⟩
    · rw [key, Equiv.symm_apply_apply]
      exact IsCocartesian.fac p f (D.transport η) φ
    · rintro χ' ⟨hχ', hfac⟩
      let χ : η ⟶ G.obj ξ := ⟨χ', hχ'⟩
      have : (adj.homEquiv η ξ).symm χ = φ' := Subtype.ext <|
        IsCocartesian.map_uniq p f (D.transport η) φ _ ((key χ).symm.trans hfac)
      exact congrArg Subtype.val ((Equiv.symm_apply_eq _).mp this)
  natural {ξ ξ'} u := by
    have := congrArg Subtype.val (adj.counit.naturality u)
    simp only [Functor.comp_map, Functor.id_map, fiber_comp_val] at this
    rw [← Category.assoc, ← D.natural', Category.assoc, this, Category.assoc]

/-- VI.10: if `f_*` exists, an inverse image functor for `f` exists iff `f_*` has a right
adjoint. -/
theorem nonempty_inverseImage_iff : Nonempty (InverseImage p f) ↔ D.functor.IsLeftAdjoint :=
  ⟨fun ⟨I⟩ ↦ ⟨I.functor, ⟨D.adjunction I⟩⟩,
    fun ⟨_, ⟨adj⟩⟩ ↦ ⟨D.inverseImageOfAdjunction adj⟩⟩

end DirectImage

/-! ### The comparisons `c^{f,g}` and `c_{f,g}` are conjugate -/

section Mates

variable {U T S : E} {f : T ⟶ S} {g : U ⟶ T}
  (Df : DirectImage p f) (Dg : DirectImage p g) (Dgf : DirectImage p (g ≫ f))

/-- The component of `c^{f,g}` at `η`. -/
noncomputable def coComparisonApp (η : Fiber p U) :
    Dgf.functor.obj η ⟶ Df.functor.obj (Dg.functor.obj η) :=
  ⟨IsCocartesian.map p (g ≫ f) (Dgf.transport η)
    (Dg.transport η ≫ Df.transport (Dg.functor.obj η)), inferInstance⟩

@[reassoc]
theorem transport_coComparisonApp (η : Fiber p U) :
    Dgf.transport η ≫ (coComparisonApp Df Dg Dgf η).val =
      Dg.transport η ≫ Df.transport (Dg.functor.obj η) :=
  IsCocartesian.fac p (g ≫ f) (Dgf.transport η) _

/-- VI.10: the comparison `c^{f,g} : (fg)_* ⟶ f_* g_*` of direct images. -/
noncomputable def coComparison : Dgf.functor ⟶ Dg.functor ⋙ Df.functor where
  app := coComparisonApp Df Dg Dgf
  naturality {η η'} u := Subtype.ext <| by
    apply IsCocartesian.ext p (g ≫ f) (Dgf.transport η)
    simp only [Functor.comp_map, fiber_comp_val, Dgf.natural'_assoc,
      transport_coComparisonApp, transport_coComparisonApp_assoc]
    rw [Df.natural', Dg.natural'_assoc]

@[reassoc]
theorem transport_coComparison (η : Fiber p U) :
    Dgf.transport η ≫ ((coComparison Df Dg Dgf).app η).val =
      Dg.transport η ≫ Df.transport (Dg.functor.obj η) :=
  transport_coComparisonApp Df Dg Dgf η

variable (K : Cleavage p)

/-- VI.10: `c^{f,g}` and `c_{f,g}` are adjoint to one another (conjugate under the
adjunctions `(fg)_* ⊣ (fg)^*` and `f_* g_* ⊣ g^* f^*`). -/
theorem conjugateEquiv_coComparison :
    conjugateEquiv ((Dg.adjunction (K.inverseImage g)).comp (Df.adjunction (K.inverseImage f)))
      (Dgf.adjunction (K.inverseImage (g ≫ f))) (coComparison Df Dg Dgf) =
        K.comparisonNatTrans f g := by
  apply NatTrans.ext
  funext ξ
  apply ((Dgf.adjunction (K.inverseImage (g ≫ f))).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, conjugateEquiv_counit,
    Adjunction.comp_counit_app]
  apply Subtype.ext
  apply IsCocartesian.ext p (g ≫ f) (Dgf.transport _)
  simp only [Functor.comp_obj, fiber_comp_val, transport_coComparison_assoc]
  rw [Df.natural'_assoc, Dgf.natural'_assoc]
  simp only [DirectImage.transport_counit, DirectImage.transport_counit_assoc]
  simp [Cleavage.inverseImage, Cleavage.comparison_fac]

/-- VI.10: `c^{f,g}` is an isomorphism iff `c_{f,g}` is. -/
theorem isIso_coComparison_iff :
    IsIso (coComparison Df Dg Dgf) ↔ IsIso (K.comparisonNatTrans f g) := by
  constructor
  · intro _
    have := conjugateEquiv_iso
      ((Dg.adjunction (K.inverseImage g)).comp (Df.adjunction (K.inverseImage f)))
      (Dgf.adjunction (K.inverseImage (g ≫ f))) (coComparison Df Dg Dgf)
    rw [conjugateEquiv_coComparison] at this
    exact this
  · intro h
    have : IsIso (conjugateEquiv
        ((Dg.adjunction (K.inverseImage g)).comp (Df.adjunction (K.inverseImage f)))
        (Dgf.adjunction (K.inverseImage (g ≫ f))) (coComparison Df Dg Dgf)) := by
      rw [conjugateEquiv_coComparison]
      exact h
    exact conjugateEquiv_of_iso
      ((Dg.adjunction (K.inverseImage g)).comp (Df.adjunction (K.inverseImage f)))
      (Dgf.adjunction (K.inverseImage (g ≫ f))) _

end Mates

/-! ### VI.10.1 -/

section

variable (p)

/-- In a fibered category every cocartesian morphism is strongly cocartesian. -/
theorem isStronglyCocartesian_of_isCocartesian [IsFibered p]
    {R S : E} (f : R ⟶ S) {a b : C} (φ : a ⟶ b) [IsCocartesian p f φ] :
    IsStronglyCocartesian p f φ where
  universal_property' {b'} g ψ hψ := by
    obtain ⟨c, β, hβ⟩ := IsPreFibered.exists_isCartesian p (rfl : p.obj b' = _) g
    have χ₀fac := IsStronglyCartesian.fac p g β (g := f) (f' := f ≫ g) rfl ψ
    let χ₀ := IsStronglyCartesian.map p g β (g := f) (f' := f ≫ g) rfl ψ
    let χ₁ := IsCocartesian.map p f φ χ₀
    refine ⟨χ₁ ≫ β, ⟨inferInstance, ?_⟩, ?_⟩
    · rw [← Category.assoc, IsCocartesian.fac]
      exact χ₀fac
    · rintro π ⟨hπ, hπfac⟩
      let π₁ := IsStronglyCartesian.map p g β (g := 𝟙 S) (f' := g) (by simp) π
      have hπ₁ : π₁ ≫ β = π := IsStronglyCartesian.fac p g β (g := 𝟙 S) (f' := g) _ π
      have hcomp : φ ≫ π₁ = χ₀ := by
        apply IsStronglyCartesian.ext p g β (g := f)
        rw [Category.assoc, hπ₁, hπfac, χ₀fac]
      rw [← hπ₁, IsCocartesian.map_uniq p f φ χ₀ π₁ hcomp]

/-- In a cofibered category every cocartesian morphism is strongly cocartesian. -/
theorem isStronglyCocartesian_of_isCocartesian_of_isCofibered [IsCofibered p]
    {R S : E} (f : R ⟶ S) {a b : C} (φ : a ⟶ b) [IsCocartesian p f φ] :
    IsStronglyCocartesian p f φ where
  universal_property' {b'} g ψ hψ := by
    obtain ⟨c, γ, hγ⟩ := IsPreCofibered.exists_isCocartesian p (IsHomLift.codomain_eq p f φ) g
    let τ := IsCocartesian.map p (f ≫ g) (φ ≫ γ) ψ
    refine ⟨γ ≫ τ, ⟨inferInstance, ?_⟩, ?_⟩
    · rw [← Category.assoc]
      exact IsCocartesian.fac p (f ≫ g) (φ ≫ γ) ψ
    · rintro π ⟨hπ, hπfac⟩
      have hπ₀ : γ ≫ IsCocartesian.map p g γ π = π := IsCocartesian.fac p g γ π
      rw [← hπ₀, IsCocartesian.map_uniq p (f ≫ g) (φ ≫ γ) ψ (IsCocartesian.map p g γ π)
        (by rw [Category.assoc, hπ₀, hπfac])]

/-- In a cofibered category every cartesian morphism is strongly cartesian. -/
theorem isStronglyCartesian_of_isCartesian_of_isCofibered [IsCofibered p]
    {R S : E} (f : R ⟶ S) {a b : C} (φ : a ⟶ b) [IsCartesian p f φ] :
    IsStronglyCartesian p f φ where
  universal_property' {a'} g φ' hφ' := by
    obtain ⟨c, α, hα⟩ := IsPreCofibered.exists_isCocartesian p (rfl : p.obj a' = _) g
    have := isStronglyCocartesian_of_isCocartesian_of_isCofibered p g α
    have hψ₀ := IsStronglyCocartesian.fac p g α (f' := g ≫ f) rfl φ'
    let ψ₀ := IsStronglyCocartesian.map p g α (f' := g ≫ f) rfl φ'
    let χ₁ := IsCartesian.map p f φ ψ₀
    refine ⟨α ≫ χ₁, ⟨inferInstance, ?_⟩, ?_⟩
    · rw [Category.assoc, IsCartesian.fac]
      exact hψ₀
    · rintro π ⟨hπ, hπfac⟩
      let π₁ := IsCocartesian.map p g α π
      have hπ₁ : α ≫ π₁ = π := IsCocartesian.fac p g α π
      have hcancel : π₁ ≫ φ = χ₁ ≫ φ := by
        apply IsStronglyCocartesian.ext p g α (g := f)
        rw [reassoc_of% hπ₁, hπfac, IsCartesian.fac, hψ₀]
      rw [← hπ₁, IsCartesian.ext p f φ π₁ χ₁ hcancel]

/-- VI.10.1: a prefibered and coprefibered category is fibered iff it is cofibered. -/
theorem isFibered_iff_isCofibered [IsPreFibered p] [IsPreCofibered p] :
    IsFibered p ↔ IsCofibered p := by
  constructor
  · intro _
    refine (isCofibered_iff_comp p).mpr fun {R S T} f g {a b c} φ ψ hφ hψ ↦ ?_
    have := isStronglyCocartesian_of_isCocartesian p f φ
    have := isStronglyCocartesian_of_isCocartesian p g ψ
    infer_instance
  · intro _
    exact (isFibered_iff_cartesian_isStronglyCartesian p).mpr fun {R S} f {a b} φ _ ↦
      isStronglyCartesian_of_isCartesian_of_isCofibered p f φ

end

end SGA.SGA1.ExposeVI
