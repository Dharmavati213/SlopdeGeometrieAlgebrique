/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# Constant schemes and étale local splitting of finite étale morphisms

For a scheme `X` and a (small) set `E`, the constant `X`-scheme with value `E` is the disjoint
union `∐_{e ∈ E} X` (`Scheme.constantScheme X E`, with structure morphism
`Scheme.constantSchemeHom X E`); it is étale over `X`.

A morphism `f : Z ⟶ A` *splits étale locally* at `a ∈ A` (`Scheme.SplitsEtaleLocallyAt f a`) if
there is an étale `g : W ⟶ A` whose image contains `a` such that `Z ×_A W` is isomorphic, over
`W`, to the constant `W`-scheme with some finite value. We show that a finite étale morphism
splits étale locally at every point (`Scheme.splitsEtaleLocallyAt_of_isFinite`): after passing to
an affine open and a basic open on which the rank is constant, this is
`Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`.

## References

* [H. W. Lenstra, *Galois theory for schemes*, 5.10][lenstraGSchemes]
* [SGA 4, Exposé IX, 2.2][sga4]
-/

universe u

open CategoryTheory Limits Opposite TensorProduct

-- Pullbacks of schemes and `Spec` of tensor products: instance arguments do not unify with the
-- default setting.
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (E : Type u)

/-- The constant `X`-scheme `∐_{e ∈ E} X` with value `E`. -/
noncomputable def constantScheme : Scheme.{u} := ∐ fun _ : E ↦ X

/-- The structure morphism of the constant `X`-scheme with value `E`. -/
noncomputable def constantSchemeHom : constantScheme X E ⟶ X := Sigma.desc fun _ ↦ 𝟙 X

/-- The inclusion of the `e`-th copy of `X` into the constant `X`-scheme. -/
noncomputable def constantSchemeι (e : E) : X ⟶ constantScheme X E := Sigma.ι (fun _ : E ↦ X) e

@[reassoc (attr := simp)]
lemma constantSchemeι_hom (e : E) : constantSchemeι X E e ≫ constantSchemeHom X E = 𝟙 X :=
  Sigma.ι_desc _ _

instance (e : E) : IsOpenImmersion (constantSchemeι X E e) :=
  inferInstanceAs (IsOpenImmersion (Sigma.ι _ _))

instance : Etale (constantSchemeHom X E) :=
  IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance

lemma constantSchemeι_surjective (y : constantScheme X E) :
    ∃ (e : E) (x : X), constantSchemeι X E e x = y := by
  obtain ⟨⟨e, x⟩, rfl⟩ := (sigmaMk (fun _ : E ↦ X)).surjective y
  exact ⟨e, x, (sigmaMk_mk (fun _ : E ↦ X) e x).symm⟩

/-- Two different copies of `X` in the constant `X`-scheme are disjoint. -/
lemma isEmpty_of_comp_constantSchemeι_eq {Z : Scheme.{u}} (a : Z ⟶ X) {e e' : E} (h : e ≠ e')
    (w : a ≫ constantSchemeι X E e = a ≫ constantSchemeι X E e') : IsEmpty Z :=
  isEmpty_of_commSq_sigmaι_of_ne (g := fun _ : E ↦ X) ⟨w⟩ h

variable {Z A : Scheme.{u}}

/-- A morphism `f : Z ⟶ A` splits étale locally at `a ∈ A` if there is an étale `g : W ⟶ A`
whose image contains `a` such that `Z ×_A W` is, as a `W`-scheme, the disjoint union of finitely
many copies of `W`. -/
def SplitsEtaleLocallyAt (f : Z ⟶ A) (a : A) : Prop :=
  ∃ (W : Scheme.{u}) (g : W ⟶ A) (_ : Etale g) (w : W) (E : Type u) (_ : Finite E), g w = a ∧
    Nonempty (Over.mk (pullback.snd f g) ≅ Over.mk (constantSchemeHom W E))

lemma SplitsEtaleLocallyAt.of_arrowIso {Z' A' : Scheme.{u}} {f : Z ⟶ A} {f' : Z' ⟶ A'}
    (e : Arrow.mk f ≅ Arrow.mk f') {a : A} (h : SplitsEtaleLocallyAt f' (e.hom.right a)) :
    SplitsEtaleLocallyAt f a := by
  obtain ⟨W, g, _, w, n, _, hw, ⟨i⟩⟩ := h
  have he : e.inv.right (e.hom.right a) = a := by
    rw [← Scheme.Hom.comp_apply, ← Arrow.comp_right, e.hom_inv_id, Arrow.id_right]
    rfl
  refine ⟨W, g ≫ e.inv.right, inferInstance, w, n, inferInstance,
    by rw [Scheme.Hom.comp_apply, hw]; exact he, ⟨?_⟩⟩
  refine Over.isoMk (f := Over.mk (pullback.snd f (g ≫ e.inv.right)))
    (g := Over.mk (pullback.snd f' g)) (asIso (pullback.map f (g ≫ e.inv.right) f' g e.hom.left
      (𝟙 W) e.hom.right (Arrow.w e.hom).symm ?_)) ?_ ≪≫ i
  · rw [Category.assoc, ← Arrow.comp_right, e.inv_hom_id, Arrow.id_right]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · simp

lemma SplitsEtaleLocallyAt.of_pullback_snd {U : Scheme.{u}} {f : Z ⟶ A} (a₀ : U ⟶ A) [Etale a₀]
    {u : U} (h : SplitsEtaleLocallyAt (pullback.snd f a₀) u) : SplitsEtaleLocallyAt f (a₀ u) := by
  obtain ⟨W, g, _, w, n, _, hw, ⟨i⟩⟩ := h
  refine ⟨W, g ≫ a₀, inferInstance, w, n, inferInstance, by rw [Scheme.Hom.comp_apply, hw], ⟨?_⟩⟩
  exact Over.isoMk (f := Over.mk (pullback.snd f (g ≫ a₀)))
    (g := Over.mk (pullback.snd (pullback.snd f a₀) g))
    (pullbackLeftPullbackSndIso f a₀ g).symm (by simp) ≪≫ i

/-- The constant `Spec T`-scheme with finite value `ι` is `Spec (ι → T)`. -/
lemma sigmaSpec_comp_Spec_map_algebraMap (T : CommRingCat.{u}) (ι : Type u) [Finite ι] :
    sigmaSpec (fun _ : ι ↦ T) ≫ Spec.map (CommRingCat.ofHom (algebraMap T (ι → T))) =
      constantSchemeHom (Spec T) ι := by
  apply Sigma.hom_ext
  intro i
  rw [ι_sigmaSpec_assoc, ← Spec.map_comp]
  change _ = constantSchemeι (Spec T) ι i ≫ constantSchemeHom (Spec T) ι
  rw [constantSchemeι_hom, ← Spec.map_id]
  rfl

/-- A finite étale morphism `Spec S ⟶ Spec R` splits étale locally. This is the geometric form
of `Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`, applied after localizing to make the
rank constant. -/
theorem splitsEtaleLocallyAt_Spec_map {R S : CommRingCat.{u}} (φ : R ⟶ S) (hf : φ.hom.Finite)
    (he : φ.hom.Etale) (p : Spec R) : SplitsEtaleLocallyAt (Spec.map φ) p := by
  let := φ.hom.toAlgebra
  have : Algebra.Etale R S := he
  have : Module.Finite R S := hf
  have := Module.FinitePresentation.of_finite_of_finitePresentation (R := R) (S := S)
  set n := Module.rankAtStalk (R := R) S p
  have hU : IsOpen {q | Module.rankAtStalk (R := R) S q = n} :=
    Module.isLocallyConstant_rankAtStalk.isOpen_fiber n
  obtain ⟨_, ⟨r, rfl⟩, hpr, hrU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show p ∈ {q | Module.rankAtStalk (R := R) S q = n} from rfl) hU
  let Rr := Localization.Away (r : R)
  have hrank : Module.rankAtStalk (R := Rr) (Rr ⊗[R] S) = n := by
    ext q
    rw [Module.rankAtStalk_baseChange, Pi.natCast_apply]
    apply hrU
    change _ ∈ (PrimeSpectrum.basicOpen (r : R) : Set (PrimeSpectrum R))
    rw [← PrimeSpectrum.localization_away_comap_range Rr (r : R)]
    exact ⟨q, rfl⟩
  obtain ⟨T, _, _, _, _, _, hT⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hrank
  obtain ⟨m, ⟨eT⟩⟩ := hT.nonempty_algEquiv_fun
  let : Algebra R T := ((algebraMap Rr T).comp (algebraMap R Rr)).toAlgebra
  have : IsScalarTower R Rr T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.Etale R T := Algebra.Etale.comp R Rr T
  let ψ : R ⟶ CommRingCat.of T := CommRingCat.ofHom (algebraMap R T)
  have hψ : Etale (Spec.map ψ) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  obtain ⟨q, hq⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R Rr)) := by
    rw [PrimeSpectrum.localization_away_comap_range Rr (r : R)]
    exact hpr
  obtain ⟨t, rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := Rr) (B := T) q
  -- the ring isomorphism `S ⊗[R] T ≃ (Fin m → T)` compatible with the maps from `T`
  let eT' : T ⊗[Rr] (Rr ⊗[R] S) ≃ₐ[T] (ULift.{u} (Fin m) → T) :=
    eT.trans (AlgEquiv.piCongrLeft' T (fun _ ↦ T) Equiv.ulift.symm)
  let e : S ⊗[R] T ≃+* (ULift.{u} (Fin m) → T) :=
    (Algebra.TensorProduct.comm R S T).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange R Rr T T S).symm.toRingEquiv.trans
        eT'.toRingEquiv)
  have he₁ (x : T) : e (1 ⊗ₜ x) = algebraMap T (ULift.{u} (Fin m) → T) x := by
    simp only [e, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
      Algebra.TensorProduct.comm_tmul]
    rw [← eT'.commutes x]
    congr 1
  refine ⟨Spec (.of T), Spec.map ψ, hψ, t, ULift.{u} (Fin m), inferInstance, ?_, ⟨?_⟩⟩
  · rw [← hq]
    rfl
  refine (Over.isoMk (f := Over.mk (constantSchemeHom (Spec (.of T)) (ULift.{u} (Fin m))))
    (g := Over.mk (pullback.snd (Spec.map φ) (Spec.map ψ)))
    (asIso (sigmaSpec (fun _ : ULift.{u} (Fin m) ↦ CommRingCat.of T)) ≪≫
      (Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso e).op) ≪≫
      (pullbackSpecIso R S T).symm) ?_).symm
  have h₁ : (pullbackSpecIso R S T).inv ≫ pullback.snd (Spec.map φ) (Spec.map ψ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := S)
        (B := T)).toRingHom) :=
    pullbackSpecIso_inv_snd R S T
  have h₂ := sigmaSpec_comp_Spec_map_algebraMap (CommRingCat.of T) (ULift.{u} (Fin m))
  have h₃ : CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := S)
        (B := T)).toRingHom ≫ CommRingCat.ofHom (e : S ⊗[R] T →+* (ULift.{u} (Fin m) → T)) =
      CommRingCat.ofHom (algebraMap T (ULift.{u} (Fin m) → T)) := by
    refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    exact he₁ x
  dsimp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.op_hom]
  erw [Category.assoc, Category.assoc, h₁, ← Spec.map_comp, h₃]
  exact h₂

/-- A finite étale morphism splits étale locally: every point of the target has an étale
neighbourhood over which the morphism becomes a finite disjoint union of copies of the base.
See [Lenstra, Galois theory for schemes, 5.10]. -/
theorem splitsEtaleLocallyAt_of_isFinite {f : Z ⟶ A} [IsFinite f] [Etale f] (a : A) :
    SplitsEtaleLocallyAt f a := by
  obtain ⟨i, u, rfl⟩ := A.affineCover.exists_eq a
  apply SplitsEtaleLocallyAt.of_pullback_snd
  have : IsAffine (pullback f (A.affineCover.f i)) :=
    isAffine_of_isAffineHom (pullback.snd f (A.affineCover.f i))
  apply SplitsEtaleLocallyAt.of_arrowIso (arrowIsoSpecΓOfIsAffine (pullback.snd f _))
  apply splitsEtaleLocallyAt_Spec_map
  · exact (pullback.snd f _).finite_appTop
  · exact (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp inferInstance

end AlgebraicGeometry.Scheme
