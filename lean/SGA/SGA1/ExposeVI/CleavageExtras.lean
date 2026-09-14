/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.Cleavage

/-!
# SGA 1, Exposé VI, VI.7.2–7.4: comparisons and normalized cleavages
-/

universe v₁ v₂ u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u₁} {C : Type u₂} [Category.{v₁} E] [Category.{v₂} C]

/-- VI.7.1: a normalized cleavage. -/
structure NormalizedCleavage (p : C ⥤ E) extends Cleavage p where
  pullback_id (S : E) : pullback (𝟙 S) = 𝟭 (Fiber p S)
  transport_id (S : E) (ξ : Fiber p S) :
    transport (𝟙 S) ξ =
      eqToHom (congrArg (fun F : Fiber p S ⥤ Fiber p S => (F.obj ξ).val)
        (pullback_id S))

namespace Cleavage

variable {p : C ⥤ E} (K : Cleavage p)

/-- VI.7.2 necessity. -/
theorem comparison_isIso_of_isFibered [IsFibered p]
    {U T S : E} (f : T ⟶ S) (g : U ⟶ T) (ξ : Fiber p S) :
    IsIso (K.comparison f g ξ) := by
  have : IsCartesian p (g ≫ f)
      (K.transport g ((K.pullback f).obj ξ) ≫ K.transport f ξ) := inferInstance
  have : IsCartesian p (g ≫ f) (K.transport (g ≫ f) ξ) :=
    K.transport_isCartesian (g ≫ f) ξ
  let e := IsCartesian.domainUniqueUpToIso p (g ≫ f)
    (K.transport (g ≫ f) ξ)
    (K.transport g ((K.pullback f).obj ξ) ≫ K.transport f ξ)
  have he : e.hom = (K.comparison f g ξ).val :=
    IsCartesian.map_uniq p (g ≫ f) (K.transport (g ≫ f) ξ) _
      e.hom (IsCartesian.fac p (g ≫ f) (K.transport (g ≫ f) ξ) _)
  have : IsHomLift p (𝟙 U) e.hom := inferInstance
  let fe : (K.pullback g).obj ((K.pullback f).obj ξ) ≅ (K.pullback (g ≫ f)).obj ξ :=
    fiberIso (p := p) (S := U) e
  have : K.comparison f g ξ = fe.hom := Subtype.ext he.symm
  rw [this]
  infer_instance

/-- Composite of cleavage transports is cartesian when the comparison is an iso. -/
theorem transport_comp_isCartesian_of_comparison_isIso
    {U T S : E} (f : T ⟶ S) (g : U ⟶ T) (ξ : Fiber p S)
    (h : IsIso (K.comparison f g ξ)) :
    IsCartesian p (g ≫ f)
      (K.transport g ((K.pullback f).obj ξ) ≫ K.transport f ξ) := by
  have : IsCartesian p (g ≫ f) (K.transport (g ≫ f) ξ) :=
    K.transport_isCartesian (g ≫ f) ξ
  have : IsHomLift p (𝟙 U) (K.comparison f g ξ).val := (K.comparison f g ξ).property
  let μ := asIso (K.comparison f g ξ)
  have : IsIso (K.comparison f g ξ).val :=
    (Fiber.fiberInclusion.mapIso μ).isIso_hom
  have : IsHomLift p (𝟙 U) (asIso (K.comparison f g ξ).val).hom := ‹_›
  rw [← K.comparison_fac f g ξ]
  exact IsCartesian.of_iso_comp (p := p) (f := g ≫ f)
    (φ := K.transport (g ≫ f) ξ) (φ' := asIso (K.comparison f g ξ).val)

/-- VI.7.2 sufficiency. -/
theorem isFibered_of_comparison_isIso
    (hiso : ∀ {U T S : E} (f : T ⟶ S) (g : U ⟶ T) (ξ : Fiber p S),
      IsIso (K.comparison f g ξ)) :
    IsFibered p := by
  have : IsPreFibered p := K.toIsPreFibered
  refine (isFibered_iff_comp p).mpr ?_
  intro R S T f g a b c φ ψ hφ hψ
  haveI : IsCartesian p g ψ := hψ
  haveI : IsCartesian p f φ := hφ
  haveI : IsHomLift p g ψ := IsCartesian.toIsHomLift
  haveI : IsHomLift p f φ := IsCartesian.toIsHomLift
  have hc : p.obj c = T := IsHomLift.codomain_eq (p := p) (f := g) (φ := ψ)
  have hb : p.obj b = S := IsHomLift.codomain_eq (p := p) (f := f) (φ := φ)
  let ξ : Fiber p T := ⟨c, hc⟩
  let η : Fiber p S := ⟨b, hb⟩
  haveI : IsCartesian p g (K.transport g ξ) := K.transport_isCartesian g ξ
  haveI : IsCartesian p f (K.transport f η) := K.transport_isCartesian f η
  let eg := IsCartesian.domainUniqueUpToIso p g (K.transport g ξ) ψ
  let ef := IsCartesian.domainUniqueUpToIso p f (K.transport f η) φ
  have heg : eg.hom ≫ K.transport g ξ = ψ :=
    IsCartesian.fac p g (K.transport g ξ) ψ
  have hef : ef.hom ≫ K.transport f η = φ :=
    IsCartesian.fac p f (K.transport f η) φ
  haveI : IsHomLift p (𝟙 S) eg.hom := inferInstance
  haveI : IsHomLift p (𝟙 R) ef.hom := inferInstance
  have hcomp : IsCartesian p (f ≫ g)
      (K.transport f ((K.pullback g).obj ξ) ≫ K.transport g ξ) :=
    K.transport_comp_isCartesian_of_comparison_isIso g f ξ (hiso g f ξ)
  let egFib : η ⟶ (K.pullback g).obj ξ := (fiberIso (p := p) (S := S) eg).hom
  have hnat := K.transport_natural f egFib
  haveI : IsIso eg.hom := inferInstance
  haveI : IsIso egFib := inferInstance
  haveI : IsIso ((K.pullback f).map egFib) := inferInstance
  haveI : IsIso ((K.pullback f).map egFib).val :=
    (Fiber.fiberInclusion.mapIso (asIso ((K.pullback f).map egFib))).isIso_hom
  haveI : IsHomLift p (𝟙 R) ((K.pullback f).map egFib).val :=
    ((K.pullback f).map egFib).property
  have hψφ :
      φ ≫ ψ =
        ef.hom ≫ ((K.pullback f).map egFib).val ≫
          (K.transport f ((K.pullback g).obj ξ) ≫ K.transport g ξ) := by
    have hegval : egFib.val = eg.hom := rfl
    calc
      φ ≫ ψ = (ef.hom ≫ K.transport f η) ≫ (eg.hom ≫ K.transport g ξ) := by
        rw [hef, heg]
      _ = ef.hom ≫ K.transport f η ≫ egFib.val ≫ K.transport g ξ := by
        simp [Category.assoc, hegval]
      _ = ef.hom ≫ ((K.pullback f).map egFib).val ≫
            K.transport f ((K.pullback g).obj ξ) ≫ K.transport g ξ := by
        rw [← Category.assoc (K.transport f η), ← hnat]
        simp
  -- Provide IsHomLift instances expected by `of_iso_comp` on `asIso`.
  haveI : IsHomLift p (𝟙 R) (asIso ((K.pullback f).map egFib).val).hom := by
    simpa using ‹IsHomLift p (𝟙 R) ((K.pullback f).map egFib).val›
  haveI : IsHomLift p (𝟙 R) (asIso ef.hom).hom := by
    simpa using ‹IsHomLift p (𝟙 R) ef.hom›
  have h1 : IsCartesian p (f ≫ g)
      (((K.pullback f).map egFib).val ≫
        (K.transport f ((K.pullback g).obj ξ) ≫ K.transport g ξ)) :=
    IsCartesian.of_iso_comp (p := p) (f := f ≫ g)
      (φ := K.transport f ((K.pullback g).obj ξ) ≫ K.transport g ξ)
      (φ' := asIso ((K.pullback f).map egFib).val)
  have h2 : IsCartesian p (f ≫ g)
      (ef.hom ≫ ((K.pullback f).map egFib).val ≫
        (K.transport f ((K.pullback g).obj ξ) ≫ K.transport g ξ)) :=
    IsCartesian.of_iso_comp (p := p) (f := f ≫ g)
      (φ := ((K.pullback f).map egFib).val ≫
        (K.transport f ((K.pullback g).obj ξ) ≫ K.transport g ξ))
      (φ' := asIso ef.hom)
  exact hψφ ▸ h2

/-- VI.7.2. -/
theorem isFibered_iff_comparison_isIso :
    IsFibered p ↔
      ∀ {U T S : E} (f : T ⟶ S) (g : U ⟶ T) (ξ : Fiber p S),
        IsIso (K.comparison f g ξ) :=
  ⟨fun _ _ _ _ f g ξ => K.comparison_isIso_of_isFibered f g ξ,
    K.isFibered_of_comparison_isIso⟩

theorem comparison_id_right_fac {T S : E} (f : T ⟶ S) (ξ : Fiber p S) :
    (K.comparison f (𝟙 T) ξ).val ≫ K.transport (𝟙 T ≫ f) ξ =
      K.transport (𝟙 T) ((K.pullback f).obj ξ) ≫ K.transport f ξ :=
  K.comparison_fac f (𝟙 T) ξ

theorem comparison_id_left_fac {T S : E} (f : T ⟶ S) (ξ : Fiber p S) :
    (K.comparison (𝟙 S) f ξ).val ≫ K.transport (f ≫ 𝟙 S) ξ =
      K.transport f ((K.pullback (𝟙 S)).obj ξ) ≫ K.transport (𝟙 S) ξ :=
  K.comparison_fac (𝟙 S) f ξ

/-- VI.7.4 B), left association path. -/
theorem comparison_assoc_left_fac {V U T S : E}
    (f : T ⟶ S) (g : U ⟶ T) (h : V ⟶ U) (ξ : Fiber p S) :
    (((K.pullback h).map (K.comparison f g ξ)).val ≫
        (K.comparison (g ≫ f) h ξ).val) ≫
      K.transport (h ≫ (g ≫ f)) ξ =
      K.transport h ((K.pullback g).obj ((K.pullback f).obj ξ)) ≫
        K.transport g ((K.pullback f).obj ξ) ≫ K.transport f ξ := by
  have hf := K.comparison_fac f g ξ
  have hgf := K.comparison_fac (g ≫ f) h ξ
  have hnat := K.transport_natural h (K.comparison f g ξ)
  calc
    (((K.pullback h).map (K.comparison f g ξ)).val ≫
          (K.comparison (g ≫ f) h ξ).val) ≫
        K.transport (h ≫ (g ≫ f)) ξ =
      ((K.pullback h).map (K.comparison f g ξ)).val ≫
        ((K.comparison (g ≫ f) h ξ).val ≫ K.transport (h ≫ (g ≫ f)) ξ) := by
      simp
    _ = ((K.pullback h).map (K.comparison f g ξ)).val ≫
        (K.transport h ((K.pullback (g ≫ f)).obj ξ) ≫
          K.transport (g ≫ f) ξ) := by
      rw [hgf]
    _ = (K.transport h ((K.pullback g).obj ((K.pullback f).obj ξ)) ≫
          (K.comparison f g ξ).val) ≫ K.transport (g ≫ f) ξ := by
      rw [← hnat]; simp
    _ = K.transport h ((K.pullback g).obj ((K.pullback f).obj ξ)) ≫
          ((K.comparison f g ξ).val ≫ K.transport (g ≫ f) ξ) := by
      simp
    _ = K.transport h ((K.pullback g).obj ((K.pullback f).obj ξ)) ≫
          (K.transport g ((K.pullback f).obj ξ) ≫ K.transport f ξ) := by
      rw [hf]
    _ = _ := by simp

/-- VI.7.4 B), right association path. -/
theorem comparison_assoc_right_fac {V U T S : E}
    (f : T ⟶ S) (g : U ⟶ T) (h : V ⟶ U) (ξ : Fiber p S) :
    ((K.comparison g h ((K.pullback f).obj ξ)).val ≫
        (K.comparison f (h ≫ g) ξ).val) ≫
      K.transport ((h ≫ g) ≫ f) ξ =
      K.transport h ((K.pullback g).obj ((K.pullback f).obj ξ)) ≫
        K.transport g ((K.pullback f).obj ξ) ≫ K.transport f ξ := by
  have hg := K.comparison_fac g h ((K.pullback f).obj ξ)
  have hfg := K.comparison_fac f (h ≫ g) ξ
  calc
    ((K.comparison g h ((K.pullback f).obj ξ)).val ≫
          (K.comparison f (h ≫ g) ξ).val) ≫
        K.transport ((h ≫ g) ≫ f) ξ =
      (K.comparison g h ((K.pullback f).obj ξ)).val ≫
        ((K.comparison f (h ≫ g) ξ).val ≫ K.transport ((h ≫ g) ≫ f) ξ) := by
      simp
    _ = (K.comparison g h ((K.pullback f).obj ξ)).val ≫
        (K.transport (h ≫ g) ((K.pullback f).obj ξ) ≫ K.transport f ξ) := by
      rw [hfg]
    _ = (K.transport h ((K.pullback g).obj ((K.pullback f).obj ξ)) ≫
          K.transport g ((K.pullback f).obj ξ)) ≫ K.transport f ξ := by
      rw [← Category.assoc, hg]
    _ = _ := by simp

/-- VI.7.4 B): the two association paths yield the same triple composite of transports. -/
theorem comparison_assoc_fac {V U T S : E}
    (f : T ⟶ S) (g : U ⟶ T) (h : V ⟶ U) (ξ : Fiber p S) :
    (((K.pullback h).map (K.comparison f g ξ)).val ≫
        (K.comparison (g ≫ f) h ξ).val) ≫
      K.transport (h ≫ (g ≫ f)) ξ =
    ((K.comparison g h ((K.pullback f).obj ξ)).val ≫
        (K.comparison f (h ≫ g) ξ).val) ≫
      K.transport ((h ≫ g) ≫ f) ξ :=
  (K.comparison_assoc_left_fac f g h ξ).trans
    (K.comparison_assoc_right_fac f g h ξ).symm


set_option linter.style.haveILetI false

/-- The identity transport of a cleavage is a vertical isomorphism. -/
theorem transport_id_isIso (S : E) (ξ : Fiber p S) :
    IsIso (K.transport (𝟙 S) ξ) := by
  haveI : IsCartesian p (𝟙 S) (K.transport (𝟙 S) ξ) := K.transport_isCartesian (𝟙 S) ξ
  exact isIso_of_vertical_isCartesian p (S := S) (K.transport (𝟙 S) ξ)

/-- `id^* ≅ 𝟭` as a natural isomorphism on the fiber. -/
noncomputable def pullbackIdIso (S : E) : K.pullback (𝟙 S) ≅ 𝟭 (Fiber p S) :=
  NatIso.ofComponents
    (fun ξ => by
      haveI : IsIso (K.transport (𝟙 S) ξ) := K.transport_id_isIso S ξ
      haveI : IsHomLift p (𝟙 S) (K.transport (𝟙 S) ξ) := inferInstance
      haveI : IsHomLift p (𝟙 S) (asIso (K.transport (𝟙 S) ξ)).hom := by
        simpa using ‹IsHomLift p (𝟙 S) (K.transport (𝟙 S) ξ)›
      exact fiberIso (p := p) (S := S) (asIso (K.transport (𝟙 S) ξ)))
    (fun {ξ η} u => by
      apply Subtype.ext
      haveI : IsIso (K.transport (𝟙 S) ξ) := K.transport_id_isIso S ξ
      haveI : IsIso (K.transport (𝟙 S) η) := K.transport_id_isIso S η
      change ((K.pullback (𝟙 S)).map u).val ≫ K.transport (𝟙 S) η =
        K.transport (𝟙 S) ξ ≫ u.val
      exact K.transport_natural (𝟙 S) u)

/-- Reindex pullback along equality of base arrows. -/
noncomputable def pullbackEqToIso {R S : E} {f g : R ⟶ S} (h : f = g) :
    K.pullback f ≅ K.pullback g :=
  eqToIso (congrArg K.pullback h)

/-- The comparison as a natural isomorphism (VI.7.2). -/
noncomputable def comparisonNatIso [IsFibered p] {U T S : E} (f : T ⟶ S) (g : U ⟶ T) :
    K.pullback f ⋙ K.pullback g ≅ K.pullback (g ≫ f) := by
  let app (ξ : Fiber p S) :
      (K.pullback g).obj ((K.pullback f).obj ξ) ≅ (K.pullback (g ≫ f)).obj ξ := by
    haveI : IsIso (K.comparison f g ξ) := K.comparison_isIso_of_isFibered f g ξ
    exact asIso (K.comparison f g ξ)
  refine NatIso.ofComponents app ?_
  intro ξ η u
  apply Subtype.ext
  haveI : IsCartesian p (g ≫ f) (K.transport (g ≫ f) η) :=
    K.transport_isCartesian (g ≫ f) η
  have hη := K.comparison_fac f g η
  have hξ := K.comparison_fac f g ξ
  have hn_f := K.transport_natural f u
  have hn_g := K.transport_natural g ((K.pullback f).map u)
  have hn_gf := K.transport_natural (g ≫ f) u
  have val_eq :
      (((K.pullback g).map ((K.pullback f).map u)).val ≫ (K.comparison f g η).val) ≫
          K.transport (g ≫ f) η =
        ((K.comparison f g ξ).val ≫ ((K.pullback (g ≫ f)).map u).val) ≫
          K.transport (g ≫ f) η := by
    calc
      (((K.pullback g).map ((K.pullback f).map u)).val ≫ (K.comparison f g η).val) ≫
            K.transport (g ≫ f) η =
        ((K.pullback g).map ((K.pullback f).map u)).val ≫
          ((K.comparison f g η).val ≫ K.transport (g ≫ f) η) := by
        simp [Category.assoc]
      _ = ((K.pullback g).map ((K.pullback f).map u)).val ≫
            (K.transport g ((K.pullback f).obj η) ≫ K.transport f η) := by
        rw [hη]
      _ = (K.transport g ((K.pullback f).obj ξ) ≫ ((K.pullback f).map u).val) ≫
            K.transport f η := by
        rw [← hn_g]; simp [Category.assoc]
      _ = K.transport g ((K.pullback f).obj ξ) ≫ (K.transport f ξ ≫ u.val) := by
        rw [Category.assoc, hn_f]
      _ = (K.transport g ((K.pullback f).obj ξ) ≫ K.transport f ξ) ≫ u.val := by
        simp [Category.assoc]
      _ = ((K.comparison f g ξ).val ≫ K.transport (g ≫ f) ξ) ≫ u.val := by
        rw [← hξ]
      _ = (K.comparison f g ξ).val ≫ (K.transport (g ≫ f) ξ ≫ u.val) := by
        simp [Category.assoc]
      _ = (K.comparison f g ξ).val ≫
            (((K.pullback (g ≫ f)).map u).val ≫ K.transport (g ≫ f) η) := by
        rw [← hn_gf]
      _ = ((K.comparison f g ξ).val ≫ ((K.pullback (g ≫ f)).map u).val) ≫
            K.transport (g ≫ f) η := by
        simp [Category.assoc]
  haveI : IsHomLift p (𝟙 U)
      (((K.pullback g).map ((K.pullback f).map u)).val ≫ (K.comparison f g η).val) := by
    have := ((K.pullback g).map ((K.pullback f).map u)).property
    have := (K.comparison f g η).property
    infer_instance
  haveI : IsHomLift p (𝟙 U)
      ((K.comparison f g ξ).val ≫ ((K.pullback (g ≫ f)).map u).val) := by
    have := (K.comparison f g ξ).property
    have := ((K.pullback (g ≫ f)).map u).property
    infer_instance
  change ((K.pullback g).map ((K.pullback f).map u)).val ≫ (app η).hom.val =
    (app ξ).hom.val ≫ ((K.pullback (g ≫ f)).map u).val
  simpa [app, asIso_hom] using
    (IsCartesian.ext (p := p) (f := g ≫ f) (φ := K.transport (g ≫ f) η)
      (((K.pullback g).map ((K.pullback f).map u)).val ≫ (K.comparison f g η).val)
      ((K.comparison f g ξ).val ≫ ((K.pullback (g ≫ f)).map u).val) val_eq)

/-- VI.7.3: pullback along a base isomorphism is an equivalence of fibers. -/
noncomputable def pullbackEquiv_of_isIso [IsFibered p] {T S : E} (f : T ≅ S) :
    Fiber p S ≌ Fiber p T :=
  CategoryTheory.Equivalence.mk
    (K.pullback f.hom)
    (K.pullback f.inv)
    ((K.pullbackIdIso S).symm ≪≫
      (K.pullbackEqToIso f.inv_hom_id.symm) ≪≫
      (K.comparisonNatIso f.hom f.inv).symm)
    ((K.comparisonNatIso f.inv f.hom) ≪≫
      (K.pullbackEqToIso f.hom_inv_id) ≪≫
      K.pullbackIdIso T)


end Cleavage

end SGA.SGA1.ExposeVI


