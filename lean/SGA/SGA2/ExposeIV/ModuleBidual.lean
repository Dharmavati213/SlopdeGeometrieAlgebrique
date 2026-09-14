/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.FiniteModuleRepresentation
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# The genuine Hom bidual with an arbitrary coefficient module

The dual is `Hom_R(-, H)` for the given module `H`. Its bidual evaluation
is the original map `x ↦ (f ↦ f x)`. When `H` is injective, actual short
exact sequences remain exact after dualizing, and hence after bidualizing.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- Actual linear Hom into the specified, arbitrary module `H`. -/
abbrev moduleHomDual (H : ModuleCat.{u} R) : (ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R :=
  (linearYoneda R (ModuleCat R)).obj H

/-- The actual double Hom functor with the same coefficient module. -/
def moduleHomBidual (H : ModuleCat.{u} R) : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  (moduleHomDual H).rightOp ⋙ moduleHomDual H

instance (H : ModuleCat.{u} R) : (moduleHomBidual H).Additive := by
  unfold moduleHomBidual
  infer_instance

/-- The canonical evaluation map, not an arbitrarily chosen bidual isomorphism. -/
def moduleBidualEvaluation (H M : ModuleCat.{u} R) : M ⟶ (moduleHomBidual H).obj M :=
  ModuleCat.ofHom (X := M) (Y := (moduleHomBidual H).obj M)
    { toFun x := ModuleCat.ofHom (X := (moduleHomDual H).obj (op M)) (Y := H)
        { toFun f := ModuleCat.Hom.hom f x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      map_add' x y := by
        apply ModuleCat.hom_ext
        ext f
        exact (ModuleCat.Hom.hom f).map_add x y
      map_smul' r x := by
        apply ModuleCat.hom_ext
        ext f
        exact (ModuleCat.Hom.hom f).map_smul r x }

@[simp] theorem moduleBidualEvaluation_apply (H M : ModuleCat.{u} R) (x : M) (f : M ⟶ H) :
    ModuleCat.Hom.hom (moduleBidualEvaluation H M x) f = f x := rfl

/-- Naturality holds for every original module morphism. -/
theorem moduleBidualEvaluation_naturality (H : ModuleCat.{u} R)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    f ≫ moduleBidualEvaluation H N =
      moduleBidualEvaluation H M ≫ (moduleHomBidual H).map f := by
  apply ModuleCat.hom_ext
  ext x
  apply ModuleCat.hom_ext
  ext g
  rfl

/-- The natural transformation from the identity to actual bidual Hom. -/
def moduleBidualEvaluationNatTrans (H : ModuleCat.{u} R) :
    𝟭 (ModuleCat.{u} R) ⟶ moduleHomBidual H where
  app M := moduleBidualEvaluation H M
  naturality {_ _} f := moduleBidualEvaluation_naturality H f

/-- Injectivity of `H` gives exactness of the original contravariant Hom,
checked through actual abelian-group Hom sequences. -/
theorem moduleHomDual_shortExact (H : ModuleCat.{u} R) [Injective H]
    {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) :
    (S.op.map (moduleHomDual H)).ShortExact := by
  apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful
    (forget₂ (ModuleCat R) AddCommGrpCat)
  exact (hS.op.map_of_exact (preadditiveYonedaObj H)).map_of_exact
    (forget₂ (ModuleCat (End H)) AddCommGrpCat)

/-- The original bidual functor preserves short exact sequences. -/
theorem moduleHomBidual_shortExact (H : ModuleCat.{u} R) [Injective H]
    {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) :
    (S.map (moduleHomBidual H)).ShortExact :=
  moduleHomDual_shortExact H (moduleHomDual_shortExact H hS)

/-- Actual canonical reflexivity is closed under extensions when `H` is
injective, by the short five lemma applied to its natural evaluation. -/
theorem moduleBidualEvaluation_isIso_of_shortExact (H : ModuleCat.{u} R) [Injective H]
    {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    [IsIso (moduleBidualEvaluation H S.X₁)] [IsIso (moduleBidualEvaluation H S.X₃)] :
    IsIso (moduleBidualEvaluation H S.X₂) := by
  let φ : S ⟶ S.map (moduleHomBidual H) :=
    S.mapNatTrans (moduleBidualEvaluationNatTrans H)
  have : IsIso φ.τ₁ := inferInstanceAs (IsIso (moduleBidualEvaluation H S.X₁))
  have : IsIso φ.τ₃ := inferInstanceAs (IsIso (moduleBidualEvaluation H S.X₃))
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ hS (moduleHomBidual_shortExact H hS)

/-- Finiteness of the two dual ends implies finiteness of the middle dual,
using the genuine short exact dual sequence. -/
theorem moduleHomDual_finite_of_shortExact (H : ModuleCat.{u} R) [Injective H]
    {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    [Module.Finite R ((moduleHomDual H).obj (op S.X₁))]
    [Module.Finite R ((moduleHomDual H).obj (op S.X₃))] :
    Module.Finite R ((moduleHomDual H).obj (op S.X₂)) := by
  let D := S.op.map (moduleHomDual H)
  have hD : D.ShortExact := moduleHomDual_shortExact H hS
  have : Module.Finite R D.X₁ :=
    inferInstanceAs (Module.Finite R ((moduleHomDual H).obj (op S.X₃)))
  have : Module.Finite R D.X₃ :=
    inferInstanceAs (Module.Finite R ((moduleHomDual H).obj (op S.X₁)))
  exact Module.Finite.of_exact
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact D).mp hD.exact)
    ((ModuleCat.epi_iff_surjective D.g).mp hD.epi_g)

end SGA.SGA2.ExposeIV
