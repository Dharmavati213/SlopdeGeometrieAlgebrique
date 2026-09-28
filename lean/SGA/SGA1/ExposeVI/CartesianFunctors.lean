/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeVI.BasedEquivalences
import SGA.SGA1.ExposeVI.Cartesian
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# SGA 1, Exposé VI, VI.5.2–5.5: cartesian functors and cartesian sections

A based functor is cartesian when it sends cartesian arrows to cartesian
arrows. Cartesian sections of `𝒳` over `E` are cartesian functors out of
the identity based category; their category is SGA's `varprojLim 𝒳 / E`.
-/

universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor ObjectProperty

variable {E : Type u} [Category.{v} E]
  {X : BasedCategory.{v₁, u₁} E} {Y : BasedCategory.{v₂, u₂} E}
  {Z : BasedCategory.{v₃, u₃} E}

/-- VI.5.2: an `E`-functor is cartesian if it preserves cartesian morphisms. -/
class IsCartesianFunctor (F : BasedFunctor X Y) : Prop where
  map_isCartesian {R S : E} {a b : X.obj} (f : R ⟶ S) (φ : a ⟶ b)
    [IsCartesian X.p f φ] : IsCartesian Y.p f (F.map φ)

attribute [instance] IsCartesianFunctor.map_isCartesian

/-- Fully faithful based functors identify morphisms over a given base arrow. -/
noncomputable def homOverEquiv_of_fullyFaithful (F : BasedFunctor X Y)
    [F.toFunctor.Full] [F.toFunctor.Faithful]
    {R S : E} (f : R ⟶ S) (a b : X.obj) :
    HomOver X.p f a b ≃ HomOver Y.p f (F.obj a) (F.obj b) where
  toFun u := ⟨F.map u.val, by have := u.property; infer_instance⟩
  invFun u :=
    letI := u.property
    ⟨F.toFunctor.preimage u.val, preimage_isHomLift F f u.val⟩
  left_inv u := Subtype.ext (F.toFunctor.preimage_map u.val)
  right_inv u := Subtype.ext (F.toFunctor.map_preimage u.val)

/-- VI.5.3(i): a based equivalence preserves cartesian morphisms. -/
theorem isCartesian_map_of_isBasedEquivalence (F : BasedFunctor X Y)
    (hF : IsBasedEquivalence F) {R S : E} {a b : X.obj} (f : R ⟶ S) (φ : a ⟶ b)
    [IsCartesian X.p f φ] : IsCartesian Y.p f (F.map φ) := by
  obtain ⟨_, _, hess⟩ := (isBasedEquivalence_iff F).mp hF
  refine (isCartesian_iff_bijective Y.p f (F.map φ)).mpr ?_
  intro y'
  constructor
  · intro u v huv
    obtain ⟨x', e, he⟩ := hess y'
    have : IsHomLift Y.p (𝟙 (Y.p.obj y')) e.hom := he
    have : IsHomLift Y.p (𝟙 (Y.p.obj y')) e.inv := IsHomLift.lift_id_inv Y.p _ e
    -- `u, v` lift `𝟙 R`, so `y'` lies over `R` and we may transport along `e`.
    have hu : IsHomLift Y.p (𝟙 R) u.val := u.property
    have hv : IsHomLift Y.p (𝟙 R) v.val := v.property
    have hR : Y.p.obj y' = R := IsHomLift.domain_eq Y.p (𝟙 R) u.val
    have : IsHomLift Y.p (𝟙 R) e.hom := hR ▸ ‹IsHomLift Y.p (𝟙 (Y.p.obj y')) e.hom›
    have : IsHomLift Y.p (𝟙 R) e.inv := hR ▸ ‹IsHomLift Y.p (𝟙 (Y.p.obj y')) e.inv›
    have : IsHomLift Y.p (𝟙 R) (e.hom ≫ u.val) :=
      IsHomLift.comp_of_lift_id Y.p R e.hom u.val
    have : IsHomLift Y.p (𝟙 R) (e.hom ≫ v.val) :=
      IsHomLift.comp_of_lift_id Y.p R e.hom v.val
    let u₀ := (homOverEquiv_of_fullyFaithful F (𝟙 R) x' a).symm ⟨e.hom ≫ u.val, inferInstance⟩
    let v₀ := (homOverEquiv_of_fullyFaithful F (𝟙 R) x' a).symm ⟨e.hom ≫ v.val, inferInstance⟩
    have hFeq : F.map u₀.val = e.hom ≫ u.val := F.toFunctor.map_preimage (e.hom ≫ u.val)
    have hFeq' : F.map v₀.val = e.hom ≫ v.val := F.toFunctor.map_preimage (e.hom ≫ v.val)
    have hcomp : u₀.val ≫ φ = v₀.val ≫ φ := by
      apply F.toFunctor.map_injective
      have huv' : u.val ≫ F.map φ = v.val ≫ F.map φ := congrArg Subtype.val huv
      simp [Functor.map_comp, hFeq, hFeq', huv']
    have := u₀.property
    have := v₀.property
    have hvu : u₀.val = v₀.val := IsCartesian.ext X.p f φ u₀.val v₀.val hcomp
    have : e.hom ≫ u.val = e.hom ≫ v.val := by
      simpa [hFeq, hFeq'] using congrArg F.map hvu
    exact Subtype.ext ((cancel_epi e.hom).mp this)
  · intro ψ
    obtain ⟨x', e, he⟩ := hess y'
    have : IsHomLift Y.p (𝟙 (Y.p.obj y')) e.hom := he
    have : IsHomLift Y.p (𝟙 (Y.p.obj y')) e.inv := IsHomLift.lift_id_inv Y.p _ e
    have hψ : IsHomLift Y.p f ψ.val := ψ.property
    have hS : Y.p.obj (F.obj b) = S := IsHomLift.codomain_eq Y.p f (F.map φ)
    have hR' : Y.p.obj y' = R := by
      have := IsHomLift.domain_eq Y.p f ψ.val
      have := IsHomLift.domain_eq Y.p f (F.map φ)
      -- `ψ` and `F.map φ` both lift `f`, so the source of `ψ` lies over `R`.
      exact IsHomLift.domain_eq Y.p f ψ.val
    have : IsHomLift Y.p (𝟙 R) e.hom := hR' ▸ ‹IsHomLift Y.p (𝟙 (Y.p.obj y')) e.hom›
    have : IsHomLift Y.p (𝟙 R) e.inv := hR' ▸ ‹IsHomLift Y.p (𝟙 (Y.p.obj y')) e.inv›
    have : IsHomLift Y.p f (e.hom ≫ ψ.val) :=
      IsHomLift.comp_lift_id_left Y.p f ψ.val e.hom
    let χ := (homOverEquiv_of_fullyFaithful F f x' b).symm ⟨e.hom ≫ ψ.val, inferInstance⟩
    have hχF : F.map χ.val = e.hom ≫ ψ.val :=
      F.toFunctor.map_preimage (e.hom ≫ ψ.val)
    have : IsHomLift X.p f χ.val := χ.property
    let χv := IsCartesian.map X.p f φ χ.val
    refine ⟨⟨e.inv ≫ F.map χv, ?_⟩, ?_⟩
    · exact IsHomLift.comp_of_lift_id Y.p R e.inv (F.map χv)
    · apply Subtype.ext
      calc
        (e.inv ≫ F.map χv) ≫ F.map φ
            = e.inv ≫ F.map (χv ≫ φ) := by simp [Functor.map_comp]
        _ = e.inv ≫ F.map χ.val := by rw [IsCartesian.fac]
        _ = e.inv ≫ e.hom ≫ ψ.val := by rw [hχF]
        _ = ψ.val := by simp

/-- VI.5.3(i), more precisely: a fully faithful based functor reflects cartesian morphisms. -/
theorem isCartesian_of_map_of_fullyFaithful (F : BasedFunctor X Y)
    [F.toFunctor.Full] [F.toFunctor.Faithful]
    {R S : E} {a b : X.obj} (f : R ⟶ S) (φ : a ⟶ b) [IsHomLift X.p f φ]
    (h : IsCartesian Y.p f (F.map φ)) : IsCartesian X.p f φ := by
  refine (isCartesian_iff_bijective X.p f φ).mpr ?_
  intro a'
  constructor
  · intro u v huv
    have : IsHomLift X.p (𝟙 R) u.val := u.property
    have : IsHomLift X.p (𝟙 R) v.val := v.property
    have : F.map u.val = F.map v.val :=
      IsCartesian.ext Y.p f (F.map φ) (F.map u.val) (F.map v.val) <| by
        simp [← Functor.map_comp, show u.val ≫ φ = v.val ≫ φ from congrArg Subtype.val huv]
    exact Subtype.ext (F.toFunctor.map_injective this)
  · intro ψ
    have : IsHomLift X.p f ψ.val := ψ.property
    have : IsHomLift Y.p f (F.map ψ.val) := inferInstance
    let χ := IsCartesian.map Y.p f (F.map φ) (F.map ψ.val)
    have : IsHomLift Y.p (𝟙 R) χ := inferInstance
    let χ₀ := (homOverEquiv_of_fullyFaithful F (𝟙 R) a' a).symm ⟨χ, inferInstance⟩
    refine ⟨χ₀, Subtype.ext ?_⟩
    apply F.toFunctor.map_injective
    have hχ₀ : F.map χ₀.val = χ := F.toFunctor.map_preimage χ
    calc
      F.map (χ₀.val ≫ φ) = F.map χ₀.val ≫ F.map φ := Functor.map_comp _ _ _
      _ = χ ≫ F.map φ := by rw [hχ₀]
      _ = F.map ψ.val := IsCartesian.fac Y.p f (F.map φ) (F.map ψ.val)

theorem isCartesianFunctor_of_isBasedEquivalence (F : BasedFunctor X Y)
    (hF : IsBasedEquivalence F) : IsCartesianFunctor F where
  map_isCartesian := isCartesian_map_of_isBasedEquivalence F hF

/-- VI.5.3(iii): the composite of cartesian functors is cartesian. -/
theorem isCartesianFunctor_comp (F : BasedFunctor X Y) (G : BasedFunctor Y Z)
    (hF : IsCartesianFunctor F) (hG : IsCartesianFunctor G) :
    IsCartesianFunctor (BasedFunctor.comp F G) where
  map_isCartesian f φ :=
    show IsCartesian Z.p f (G.map (F.map φ)) from hG.map_isCartesian f (F.map φ)

theorem isCartesianFunctor_id : IsCartesianFunctor (BasedFunctor.id X) where
  map_isCartesian f φ :=
    show IsCartesian X.p f φ from inferInstance

/-- VI.5.3(ii): cartesianness is invariant under based isomorphism of functors. -/
theorem isCartesianFunctor_of_iso {F G : BasedFunctor X Y} (α : F ≅ G)
    (hF : IsCartesianFunctor F) : IsCartesianFunctor G where
  map_isCartesian {R S a b} f φ hφ := by
    have hnat : α.hom.app a ≫ G.map φ = F.map φ ≫ α.hom.app b := (α.hom.naturality φ).symm
    have ha : X.p.obj a = R := IsHomLift.domain_eq X.p f φ
    have hb : X.p.obj b = S := IsHomLift.codomain_eq X.p f φ
    have : IsHomLift Y.p (𝟙 R) (α.hom.app a) := ha ▸ α.hom.isHomLift' a
    have : IsHomLift Y.p (𝟙 S) (α.hom.app b) := hb ▸ α.hom.isHomLift' b
    have : IsCartesian Y.p f (F.map φ) := hF.map_isCartesian f φ
    let μ := asIso (α.hom.app a)
    let ν := asIso (α.hom.app b)
    have : IsHomLift Y.p (𝟙 R) μ.hom := ‹IsHomLift Y.p (𝟙 R) (α.hom.app a)›
    have : IsHomLift Y.p (𝟙 S) ν.hom := ‹IsHomLift Y.p (𝟙 S) (α.hom.app b)›
    exact (isCartesian_iff_of_vertical_iso Y.p f (F.map φ) (G.map φ) μ ν hnat).mp ‹_›

/-- VI.5.2: the full subcategory of cartesian `E`-functors. -/
def cartesianFunctorProperty : ObjectProperty (BasedFunctor X Y) :=
  fun F => IsCartesianFunctor F

abbrev CartesianFunctors (X : BasedCategory.{v₁, u₁} E)
    (Y : BasedCategory.{v₂, u₂} E) :=
  (cartesianFunctorProperty (X := X) (Y := Y)).FullSubcategory

instance : Category (CartesianFunctors X Y) :=
  inferInstanceAs (Category (cartesianFunctorProperty (X := X) (Y := Y)).FullSubcategory)

/-- VI.5.5: cartesian sections of `𝒳` over `E`. -/
abbrev cartesianLimit (X : BasedCategory.{v₁, u₁} E) :=
  CartesianFunctors (BasedCategory.ofFunctor (𝟭 E)) X

/-- VI.5.4: precomposition with a based equivalence preserves cartesianness both ways. -/
theorem isCartesianFunctor_precomp_iff (F : BasedFunctor X Y) (hF : IsBasedEquivalence F)
    (G : BasedFunctor Y Z) :
    IsCartesianFunctor (BasedFunctor.comp F G) ↔ IsCartesianFunctor G := by
  constructor
  · intro h
    obtain ⟨Q⟩ := hF
    have hinv : IsCartesianFunctor Q.inverse :=
      isCartesianFunctor_of_isBasedEquivalence Q.inverse Q.isBasedEquivalence_inverse
    have : IsCartesianFunctor (BasedFunctor.comp Q.inverse (BasedFunctor.comp F G)) :=
      isCartesianFunctor_comp Q.inverse (BasedFunctor.comp F G) hinv h
    let β : BasedFunctor.comp Q.inverse (BasedFunctor.comp F G) ≅ G :=
      (basedPostcomp G).mapIso Q.counitIso
    exact isCartesianFunctor_of_iso β this
  · intro h
    exact isCartesianFunctor_comp F G (isCartesianFunctor_of_isBasedEquivalence F hF) h

/-- VI.5.4: postcomposition with a based equivalence preserves cartesianness both ways. -/
theorem isCartesianFunctor_postcomp_iff (F : BasedFunctor X Y) (hF : IsBasedEquivalence F)
    (G : BasedFunctor Z X) :
    IsCartesianFunctor (BasedFunctor.comp G F) ↔ IsCartesianFunctor G := by
  constructor
  · intro h
    obtain ⟨Q⟩ := hF
    have hinv : IsCartesianFunctor Q.inverse :=
      isCartesianFunctor_of_isBasedEquivalence Q.inverse Q.isBasedEquivalence_inverse
    let β : G ≅ BasedFunctor.comp (BasedFunctor.comp G F) Q.inverse :=
      (basedPrecomp G).mapIso Q.unitIso
    have : IsCartesianFunctor (BasedFunctor.comp (BasedFunctor.comp G F) Q.inverse) :=
      isCartesianFunctor_comp (BasedFunctor.comp G F) Q.inverse h hinv
    exact isCartesianFunctor_of_iso β.symm this
  · intro h
    exact isCartesianFunctor_comp G F h (isCartesianFunctor_of_isBasedEquivalence F hF)

end SGA.SGA1.ExposeVI

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor ObjectProperty

variable {E : Type u} [Category.{v} E]
  {X : BasedCategory.{v₁, u₁} E} {Y : BasedCategory.{v₂, u₂} E}

/-- VI.5.3(ii): cartesian functors are closed under isomorphism. -/
instance cartesianFunctorProperty_isClosedUnderIsomorphisms :
    (cartesianFunctorProperty (X := X) (Y := Y)).IsClosedUnderIsomorphisms :=
  ⟨fun e h ↦ isCartesianFunctor_of_iso e h⟩

namespace BasedQuasiInverse

variable {F : BasedFunctor X Y} (Q : BasedQuasiInverse F) (Z : BasedCategory.{v₃, u₃} E)

/-- VI.5.4: for an `E`-equivalence `F : 𝒳 ⥤ 𝒴`, `G ↦ G ∘ F` is an equivalence
`Cart_E(𝒴, 𝒵) ≌ Cart_E(𝒳, 𝒵)`. -/
def cartesianPrecompEquivalence : CartesianFunctors Y Z ≌ CartesianFunctors X Z :=
  (Q.precompEquivalence Z).congrFullSubcategory (by
    funext G
    exact propext (isCartesianFunctor_precomp_iff F ⟨Q⟩ G))

/-- VI.5.4: for an `E`-equivalence `F : 𝒳 ⥤ 𝒴`, `G ↦ F ∘ G` is an equivalence
`Cart_E(𝒵, 𝒳) ≌ Cart_E(𝒵, 𝒴)`. -/
def cartesianPostcompEquivalence : CartesianFunctors Z X ≌ CartesianFunctors Z Y :=
  (Q.postcompEquivalence Z).congrFullSubcategory (by
    funext G
    exact propext (isCartesianFunctor_postcomp_iff F ⟨Q⟩ G))

end BasedQuasiInverse

end SGA.SGA1.ExposeVI

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor ObjectProperty

variable {E : Type u} [Category.{v} E]
  {X : BasedCategory.{v₁, u₁} E} {Y : BasedCategory.{v₂, u₂} E} {Z : BasedCategory.{v₃, u₃} E}

/-- Remark after VI.5.4: the composition functor restricts to cartesian functors,
`Cart_E(𝒳, 𝒴) × Cart_E(𝒴, 𝒵) ⥤ Cart_E(𝒳, 𝒵)`. -/
def cartesianComposition :
    CartesianFunctors X Y × CartesianFunctors Y Z ⥤ CartesianFunctors X Z :=
  cartesianFunctorProperty.lift
    ((cartesianFunctorProperty.ι.prod cartesianFunctorProperty.ι) ⋙ basedComposition)
    (fun FG ↦ isCartesianFunctor_comp FG.1.obj FG.2.obj FG.1.property FG.2.property)

/-- VI.5.5: `lim(𝒳/E)` is functorial in `𝒳` for cartesian functors: a cartesian functor
`G : 𝒳 ⥤ 𝒴` induces `lim(𝒳/E) ⥤ lim(𝒴/E)`. -/
def cartesianLimitMap (G : BasedFunctor X Y) (hG : IsCartesianFunctor G) :
    cartesianLimit X ⥤ cartesianLimit Y :=
  cartesianFunctorProperty.lift (cartesianFunctorProperty.ι ⋙ basedPostcomp G)
    (fun s ↦ isCartesianFunctor_comp s.obj G s.property hG)

end SGA.SGA1.ExposeVI
