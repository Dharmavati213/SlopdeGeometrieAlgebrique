/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.SpectralObjectPreadditive
import SGA.SGA2.ExposeV.RingedModuleGlobalAction

/-!
# Lifting an actual ring action on an additive spectral object to modules

The ring acts by the original spectral-object endomorphisms. Hence interval
maps and connecting maps are linear. Faithfulness and exactness of forgetting
module structure retain the three original exactness assertions. The result
is a genuine spectral object in modules, not just a collection of modules
on otherwise unrelated page terms.
-/

noncomputable section

universe u v

open CategoryTheory Limits ComposableArrows

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {B : Type u} [Ring B]

/-- A genuine ring action by additive endomorphisms gives its original module structure. -/
@[instance_reducible]
def moduleOfAdditiveEndRingHom (A : AddCommGrpCat.{v}) (ρ : B →+* End A) : Module B A where
  smul r x := AddCommGrpCat.Hom.hom (ρ r) x
  one_smul x := ConcreteCategory.congr_hom ρ.map_one x
  mul_smul r s x := ConcreteCategory.congr_hom (ρ.map_mul r s) x
  smul_zero r := (ρ r).hom.map_zero
  smul_add r x y := (ρ r).hom.map_add x y
  add_smul r s x := ConcreteCategory.congr_hom (ρ.map_add r s) x
  zero_smul x := ConcreteCategory.congr_hom ρ.map_zero x

variable {ι : Type*} [Category ι]
  (S : Abelian.SpectralObject AddCommGrpCat.{v} ι) (ρ : B →+* End S)

/-- The actual scalar action on one degree and interval of the original spectral object. -/
def spectralObjectTermScalarRingHom (n : ℤ) (D : ComposableArrows ι 1) :
    B →+* End ((S.H n).obj D) :=
  (additiveEndRingHom (ExposeI.spectralObjectEvaluation n D) S).comp ρ

/-- An original spectral-object term with the module structure induced by the retained action. -/
def spectralObjectModuleObj (n : ℤ) (D : ComposableArrows ι 1) : ModuleCat.{v} B :=
  letI := moduleOfAdditiveEndRingHom ((S.H n).obj D) (spectralObjectTermScalarRingHom S ρ n D)
  ModuleCat.of B ((S.H n).obj D)

/-- The original interval maps become linear for the retained scalar action. -/
def spectralObjectModuleFunctor (n : ℤ) : ComposableArrows ι 1 ⥤ ModuleCat.{v} B where
  obj D := spectralObjectModuleObj S ρ n D
  map {D E} a := ModuleCat.ofHom
    (X := spectralObjectModuleObj S ρ n D) (Y := spectralObjectModuleObj S ρ n E)
    { toFun := (S.H n).map a
      map_add' x y := ((S.H n).map a).hom.map_add x y
      map_smul' r x := by
        change (S.H n).map a (((ρ r).hom n).app _ x) =
          ((ρ r).hom n).app _ ((S.H n).map a x)
        exact (ConcreteCategory.congr_hom (((ρ r).hom n).naturality a) x).symm }
  map_id D := by
    ext x
    exact ConcreteCategory.congr_hom ((S.H n).map_id D) x
  map_comp a b := by
    ext x
    exact ConcreteCategory.congr_hom ((S.H n).map_comp a b) x

/-- Forgetting the termwise module structures gives the original degree functor and its maps. -/
def spectralObjectModuleFunctorForgetIso (n : ℤ) :
    spectralObjectModuleFunctor S ρ n ⋙ forget₂ (ModuleCat B) AddCommGrpCat ≅ S.H n :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- The original connecting map is linear because scalars are spectral-object endomorphisms. -/
def spectralObjectModuleδ (n m : ℤ) (h : n + 1 = m) (D : ComposableArrows ι 2) :
    (spectralObjectModuleFunctor S ρ n).obj ((functorArrows ι 1 2 2).obj D) ⟶
      (spectralObjectModuleFunctor S ρ m).obj ((functorArrows ι 0 1 2).obj D) :=
  ModuleCat.ofHom
    (X := (spectralObjectModuleFunctor S ρ n).obj ((functorArrows ι 1 2 2).obj D))
    (Y := (spectralObjectModuleFunctor S ρ m).obj ((functorArrows ι 0 1 2).obj D))
    { toFun := (S.δ' n m h).app D
      map_add' x y := ((S.δ' n m h).app D).hom.map_add x y
      map_smul' r x := by
        obtain ⟨i, j, k, f, g, rfl⟩ := mk₂_surjective D
        exact (ConcreteCategory.congr_hom ((ρ r).comm n m h f g) x).symm }

/-- Actual three-term exactness is reflected by forgetting module structure. -/
theorem moduleComposableArrows_exact_of_forget {L M N : ModuleCat.{v} B}
    (a : L ⟶ M) (b : M ⟶ N)
    (h : (mk₂ ((forget₂ (ModuleCat B) AddCommGrpCat).map a)
      ((forget₂ (ModuleCat B) AddCommGrpCat).map b)).Exact) : (mk₂ a b).Exact := by
  let F := forget₂ (ModuleCat B) AddCommGrpCat
  have hzero : F.map a ≫ F.map b = 0 := h.zero 0
  have hab : a ≫ b = 0 := F.map_injective (by
    simpa only [Functor.map_comp, Functor.map_zero] using hzero)
  let T := ShortComplex.mk a b hab
  have hT : (T.map F).Exact := h.exact 0
  exact ((T.exact_map_iff_of_faithful F).mp hT).exact_toComposableArrows

/-- The original additive spectral object with its genuine retained module action. -/
def spectralObjectModuleLift : Abelian.SpectralObject (ModuleCat.{v} B) ι where
  H n := spectralObjectModuleFunctor S ρ n
  δ' n m h :=
    { app D := spectralObjectModuleδ S ρ n m h D
      naturality {D E} a := by
        ext x
        exact ConcreteCategory.congr_hom ((S.δ' n m h).naturality a) x }
  exact₁' n m h D := moduleComposableArrows_exact_of_forget _ _ (S.exact₁' n m h D)
  exact₂' n D := moduleComposableArrows_exact_of_forget _ _ (S.exact₂' n D)
  exact₃' n m h D := moduleComposableArrows_exact_of_forget _ _ (S.exact₃' n m h D)

/-- The lifted connecting maps forget to the original connecting maps, without conjugation. -/
@[simp]
theorem spectralObjectModuleLift_δ_forget {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
    (n m : ℤ) (h : n + 1 = m) :
    (forget₂ (ModuleCat B) AddCommGrpCat).map
        ((spectralObjectModuleLift S ρ).δ f g n m h) = S.δ f g n m h := rfl

end SGA.SGA2.ExposeV
