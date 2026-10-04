/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXIII.ProperSmoothRegularGeneric
import SGA.SGA1.ExposeX.TameLiftingGeneral
import SGA.SGA1.ExposeXIII.ProperSmoothTame

/-!
# SGA 1, Exposé XIII, 4.4 over a regular base: the codimension-one step

Let `f : X ⟶ S` be proper and smooth with geometrically connected fibres and with a section `g`,
`k : Spec K ⟶ S` a point (in the application the generic point of `S`), `Y = X_K` and `W` an étale
covering of `Y` on whose fibre the good elements of `π₁(Y)` act trivially (the covering built by
`exists_isConnected_mono_forall_isGoodFor_of_section`). Let `R` be a complete discrete valuation
ring with separably closed residue field of characteristic exponent `q`, `ρ : Spec R ⟶ S` a
morphism whose restriction to the fraction field `F` of `R` factors through `k`, and assume that no
prime of `L` divides `q`. Then the inverse image of `W` on `X_F = Y ×_K F` extends to an étale
covering of `X_R = X ×_S R` (`exists_iso_pullback_fibreMap_of_goodActsTrivially`).

This replaces, in the proof of the second part of XIII.4.4 over a regular base, SGA's use of
`R¹f_*` (XIII.4.3.1) at the codimension-one points of the base: the input is the core of X.3.8
over `R` (`SGA.SGA1.ExposeX.tameLiftingDVRStatement`), through the group-theoretic criterion
`exists_iso_of_forall_isGoodFor` and `isGoodFor_of_mem_ker_of_conj`.

* `exists_autHom_eq_conj`: the homomorphisms `autHom` of two isomorphic functors agree up to an
  inner automorphism;
* `FundamentalGroup.exists_map_comp_eq_conj`: two ways of going around a commutative square of
  schemes induce the same map of fundamental groups up to an inner automorphism (V.6.3);
* `FactorsPrimeTo.ker_le`: the kernel of a homomorphism satisfying `FactorsPrimeTo` lies in every
  open normal subgroup of index prime to `q`;
* `fibreMap`, `secOf`: the maps `X_{T'} ⟶ X_T` and the sections `T ⟶ X_T` induced by `g`.
-/

universe u w

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory IsLocalRing

namespace SGA.SGA1.ExposeXIII

section AutHom

variable {C : Type*} [Category C] {C' : Type*} [Category C'] {F : C ⥤ FintypeCat.{w}}
  {F' : C' ⥤ FintypeCat.{w}}

/-- Conjugation by an automorphism `φ` of a fibre functor is the inner automorphism by `φ`. -/
lemma conjAut_eq_mul_mul_inv (φ : F ≅ F) (σ : Aut F) :
    φ.conjAut σ = (show Aut F from φ) * σ * (show Aut F from φ)⁻¹ := by
  apply Iso.ext
  change φ.inv ≫ σ.hom ≫ φ.hom = φ.inv ≫ σ.hom ≫ φ.hom
  rfl

/-- The homomorphisms `autHom` attached to two isomorphic functors agree up to an inner
automorphism. -/
lemma exists_autHom_eq_conj {H H' : C ⥤ C'} (ρ : H ≅ H') (u : H ⋙ F' ≅ F) (u' : H' ⋙ F' ≅ F) :
    ∃ c : Aut F, ∀ σ, autHom H u σ = c * autHom H' u' σ * c⁻¹ := by
  let φ : F ≅ F := u'.symm ≪≫ Functor.isoWhiskerRight ρ.symm F' ≪≫ u
  refine ⟨φ, fun σ ↦ ?_⟩
  have hu : u = (Functor.isoWhiskerRight ρ F' ≪≫ u') ≪≫ φ := by
    ext X
    simp [φ, ← Functor.map_comp_assoc]
  rw [hu, autHom_trans, MonoidHom.comp_apply, autHom_congr, MulEquiv.coe_toMonoidHom,
    conjAut_eq_mul_mul_inv]

end AutHom

/-- The kernel of a homomorphism satisfying `FactorsPrimeTo sp q` (the form of X.3.8) lies in every
open normal subgroup of index prime to `q`. -/
theorem FactorsPrimeTo.ker_le {G₁ : Type u} {G₀ : Type*} [Group G₁] [TopologicalSpace G₁]
    [IsTopologicalGroup G₁] [CompactSpace G₁] [Group G₀] [TopologicalSpace G₀] {sp : G₁ →* G₀}
    {q : ℕ} (h : ExposeX.FactorsPrimeTo sp q) {N : Subgroup G₁} [N.Normal]
    (hN : IsOpen (N : Set G₁)) (hq : N.index.Coprime q) : sp.ker ≤ N := by
  have hfin : Finite (G₁ ⧸ N) := Subgroup.quotient_finite_of_isOpen N hN
  obtain ⟨g', -, hg'⟩ := @h (G₁ ⧸ N) _ hfin _ (QuotientGroup.discreteTopology hN)
    (by rwa [← Subgroup.index_eq_card]) (QuotientGroup.mk' N) continuous_quot_mk
  intro x hx
  have : QuotientGroup.mk' N x = 1 := by
    rw [← hg', MonoidHom.comp_apply, hx, map_one]
  exact (QuotientGroup.eq_one_iff x).mp this

section Scheme

variable {Ω : Type u} [Field Ω]

/-- V.6.3: the two composites around a commutative square of schemes `g₁ ≫ g₂ = g₁' ≫ g₂'` induce
the same map of fundamental groups, up to the transports to a common geometric point `v` and an
inner automorphism of `π₁(V, v)`. -/
theorem FundamentalGroup.exists_map_comp_eq_conj {T U U' V : Scheme.{u}} (g₁ : T ⟶ U)
    (g₂ : U ⟶ V) (g₁' : T ⟶ U') (g₂' : U' ⟶ V) (w : g₁ ≫ g₂ = g₁' ≫ g₂')
    (y : Spec (.of Ω) ⟶ T) {v : Spec (.of Ω) ⟶ V} (h : (y ≫ g₁) ≫ g₂ = v)
    (h' : (y ≫ g₁') ≫ g₂' = v) :
    ∃ c : FundamentalGroup v, ∀ z : FundamentalGroup y,
      (ExposeV.FEt.fiberCongr Ω h).conjAut
          (FundamentalGroup.map g₂ (y ≫ g₁) (FundamentalGroup.map g₁ y z)) =
        c * (ExposeV.FEt.fiberCongr Ω h').conjAut
          (FundamentalGroup.map g₂' (y ≫ g₁') (FundamentalGroup.map g₁' y z)) * c⁻¹ := by
  have e₁ : (ExposeV.FEt.fiberCongr Ω h).conjAut.toMonoidHom.comp
      ((FundamentalGroup.map g₂ (y ≫ g₁)).comp (FundamentalGroup.map g₁ y)) =
      autHom (ExposeV.FEt.pullback g₂ ⋙ ExposeV.FEt.pullback g₁)
        ((Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (fiberPullbackIso g₁ y) ≪≫
          fiberPullbackIso g₂ (y ≫ g₁)) ≪≫ ExposeV.FEt.fiberCongr Ω h) := by
    rw [FundamentalGroup.map_eq_autHom, FundamentalGroup.map_eq_autHom, autHom_comp,
      autHom_trans _ _ (ExposeV.FEt.fiberCongr Ω h)]
  have e₂ : (ExposeV.FEt.fiberCongr Ω h').conjAut.toMonoidHom.comp
      ((FundamentalGroup.map g₂' (y ≫ g₁')).comp (FundamentalGroup.map g₁' y)) =
      autHom (ExposeV.FEt.pullback g₂' ⋙ ExposeV.FEt.pullback g₁')
        ((Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (fiberPullbackIso g₁' y) ≪≫
          fiberPullbackIso g₂' (y ≫ g₁')) ≪≫ ExposeV.FEt.fiberCongr Ω h') := by
    rw [FundamentalGroup.map_eq_autHom, FundamentalGroup.map_eq_autHom, autHom_comp,
      autHom_trans _ _ (ExposeV.FEt.fiberCongr Ω h')]
  let ρ : ExposeV.FEt.pullback g₂ ⋙ ExposeV.FEt.pullback g₁ ≅
      ExposeV.FEt.pullback g₂' ⋙ ExposeV.FEt.pullback g₁' :=
    (MorphismProperty.Over.pullbackComp g₁ g₂).symm ≪≫
      MorphismProperty.Over.pullbackComp g₁' g₂' (g₁ ≫ g₂) w
  obtain ⟨c, hc⟩ := exists_autHom_eq_conj ρ _ _
  refine ⟨c, fun z ↦ ?_⟩
  have := hc z
  rw [← e₁, ← e₂] at this
  exact this

/-- The transport along `rfl` is the identity. -/
@[simp]
lemma fiberCongr_rfl_conjAut {T : Scheme.{u}} {x : Spec (.of Ω) ⟶ T} (σ : FundamentalGroup x) :
    (ExposeV.FEt.fiberCongr Ω (rfl : x = x)).conjAut σ = σ := by
  apply Iso.ext
  change (ExposeV.FEt.fiberCongr Ω (rfl : x = x)).inv ≫ σ.hom ≫
    (ExposeV.FEt.fiberCongr Ω (rfl : x = x)).hom = σ.hom
  rw [show (ExposeV.FEt.fiberCongr Ω (rfl : x = x)).hom = 𝟙 _ from rfl,
    show (ExposeV.FEt.fiberCongr Ω (rfl : x = x)).inv = 𝟙 _ from rfl, Category.id_comp,
    Category.comp_id]

/-- Transports along equal geometric points compose. -/
lemma fiberCongr_conjAut_conjAut {T : Scheme.{u}} {x x' x'' : Spec (.of Ω) ⟶ T} (h₁ : x = x')
    (h₂ : x' = x'') (σ : FundamentalGroup x) :
    (ExposeV.FEt.fiberCongr Ω h₂).conjAut ((ExposeV.FEt.fiberCongr Ω h₁).conjAut σ) =
      (ExposeV.FEt.fiberCongr Ω (h₁.trans h₂)).conjAut σ := by
  subst h₁ h₂
  rw [fiberCongr_rfl_conjAut, fiberCongr_rfl_conjAut]

/-- `π₁` of an isomorphism of schemes, as an isomorphism of topological groups. -/
noncomputable def FundamentalGroup.mapContinuousMulEquiv [IsSepClosed Ω] {T T' : Scheme.{u}}
    [ConnectedSpace T] (θ : T ⟶ T') [IsIso θ] (y : Spec (.of Ω) ⟶ T) :
    FundamentalGroup y ≃ₜ* FundamentalGroup (y ≫ θ) :=
  ExposeV.autContinuousMulEquiv (ExposeV.FEt.pullback θ) (ExposeV.FEt.pullbackFiberIso Ω θ y)

lemma FundamentalGroup.mapContinuousMulEquiv_apply [IsSepClosed Ω] {T T' : Scheme.{u}}
    [ConnectedSpace T] (θ : T ⟶ T') [IsIso θ] (y : Spec (.of Ω) ⟶ T) (z : FundamentalGroup y) :
    FundamentalGroup.mapContinuousMulEquiv θ y z = FundamentalGroup.map θ y z :=
  rfl

end Scheme

section Fibres

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The morphism `X_{T'} ⟶ X_T` induced by a morphism `m : T' ⟶ T` over `S`. -/
noncomputable def fibreMap {T T' : Scheme.{u}} {a : T' ⟶ S} {b : T ⟶ S} (m : T' ⟶ T)
    (hm : m ≫ b = a) : pullback f a ⟶ pullback f b :=
  pullback.map f a f b (𝟙 X) m (𝟙 S) (by simp) (by simp [hm])

variable {T T' : Scheme.{u}} {a : T' ⟶ S} {b : T ⟶ S} (m : T' ⟶ T) (hm : m ≫ b = a)

@[reassoc (attr := simp)]
lemma fibreMap_fst : fibreMap f m hm ≫ pullback.fst f b = pullback.fst f a := by
  rw [fibreMap, pullback.map, pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)]
lemma fibreMap_snd : fibreMap f m hm ≫ pullback.snd f b = pullback.snd f a ≫ m := by
  rw [fibreMap, pullback.map, pullback.lift_snd]

/-- `X_{T'} = X_T ×_T T'`. -/
lemma isPullback_fibreMap :
    IsPullback (fibreMap f m hm) (pullback.snd f a) (pullback.snd f b) m :=
  IsPullback.of_right (by rw [fibreMap_fst, hm]; exact IsPullback.of_hasPullback f a)
    (fibreMap_snd f m hm) (IsPullback.of_hasPullback f b)

variable {f} {g : S ⟶ X} (hg : g ≫ f = 𝟙 S)

/-- The section `T ⟶ X_T` induced by a section `g` of `f`. -/
noncomputable def secOf (a : T ⟶ S) : T ⟶ pullback f a :=
  pullback.lift (a ≫ g) (𝟙 T) (by rw [Category.assoc, hg, Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)]
lemma secOf_fst (a : T ⟶ S) : secOf hg a ≫ pullback.fst f a = a ≫ g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma secOf_snd (a : T ⟶ S) : secOf hg a ≫ pullback.snd f a = 𝟙 T :=
  pullback.lift_snd _ _ _

@[reassoc]
lemma secOf_fibreMap : secOf hg a ≫ fibreMap f m hm = m ≫ secOf hg b := by
  apply pullback.hom_ext
  · simp [← hm]
  · simp

end Fibres

section CodimOne

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [IsSepClosed (ResidueField R)]

/-- The core of X.3.8 (`SGA.SGA1.ExposeX.tameLiftingDVRStatement`) at a geometric point of
`Spec R` over the generic point, given by an injective `φ : R → Ω₁`. -/
theorem factorsPrimeTo_map_fst_of_injective {Z : Scheme.{u}} (fR : Z ⟶ Spec (.of R)) [IsProper fR]
    [Smooth fR] [GeometricallyConnected fR] (Ω₁ : Type u) [Field Ω₁] [IsAlgClosed Ω₁]
    (φ : R →+* Ω₁) (hφ : Function.Injective φ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (a : Spec (.of Ω) ⟶ pullback fR (Spec.map (CommRingCat.ofHom φ))) :
    ExposeX.FactorsPrimeTo
      (FundamentalGroup.map (pullback.fst fR (Spec.map (CommRingCat.ofHom φ))) a)
      (ringExpChar (ResidueField R)) :=
  letI := φ.toAlgebra
  ExposeX.tameLiftingDVRStatement R fR Ω₁ hφ Ω a

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
  {g : S ⟶ X} (hg : g ≫ f = 𝟙 S) {K : Type u} [Field K] (k : Spec (.of K) ⟶ S)

/-- The property of the covering `W` of `X_K = X ×_S K` built in
`exists_isConnected_mono_forall_isGoodFor_of_section`: the good elements of `π₁(X_K)` (for the
section induced by `g`, at the point of `X_K` on the section over `t`, and for the open normal
subgroups of `L`-index of `π₁(X_K̄)`) act trivially on the fibre of `W`. -/
def GoodActsTrivially (L : Set ℕ) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ Spec (.of K)) (W : ExposeV.FEt (pullback f k)) : Prop :=
  ∀ σ : FundamentalGroup
      (basePt (pullback.snd f k) (secOf hg k) (secOf_snd hg k) t ≫ pullback.fst _ t),
    IsGoodFor (FundamentalGroup.map (pullback.snd f k)
        (basePt (pullback.snd f k) (secOf hg k) (secOf_snd hg k) t ≫ pullback.fst _ t)).ker
      (sectionHom (pullback.snd f k) (secOf hg k) (secOf_snd hg k) t)
      (lIndexSubgroups L (FundamentalGroup.map (pullback.snd f k)
        (basePt (pullback.snd f k) (secOf hg k) (secOf_snd hg k) t ≫ pullback.fst _ t)).ker) σ →
    ∀ w : (ExposeV.FEt.fiber Ω
      (basePt (pullback.snd f k) (secOf hg k) (secOf_snd hg k) t ≫ pullback.fst _ t)).obj W,
      σ • w = w

/-- **The codimension-one step** of the second part of XIII.4.4 over a regular base. Let
`f : X ⟶ S` be proper and smooth with geometrically connected fibres and with a section `g`,
`k : Spec K ⟶ S`, and `W` an étale covering of `X_K` on whose fibre the good elements of `π₁(X_K)`
act trivially (`GoodActsTrivially`, at the point over `t = t_F ≫ j`). Let `R` be a complete
discrete valuation ring with separably closed residue field, `F` its fraction field,
`ρ : Spec R ⟶ S` with `Spec F ⟶ Spec R ⟶ S` equal to `j ≫ k` for some `j : Spec F ⟶ Spec K`, and
assume that no prime of `L` divides the characteristic exponent of the residue field of `R`. Then
the inverse image of `W` on `X_F` extends to an étale covering of `X_R = X ×_S R`.

The kernel of `π₁(X_F) → π₁(X_R)` maps to good elements of `π₁(X_K)`
(`isGoodFor_of_mem_ker_of_conj`, whose main input is the core of X.3.8 over `R`,
`factorsPrimeTo_map_fst_of_injective`), so
`exists_iso_of_forall_isGoodFor` applies. -/
theorem exists_iso_pullback_fibreMap_of_goodActsTrivially (L : Set ℕ)
    (hL : ∀ ℓ ∈ L, ¬ ℓ ∣ ringExpChar (ResidueField R))
    (ρ : Spec (.of R) ⟶ S) (F : Type u) [Field F] [Algebra R F] [IsFractionRing R F]
    (j : Spec (.of F) ⟶ Spec (.of K))
    (hj : Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ ρ = j ≫ k)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (tF : Spec (.of Ω) ⟶ Spec (.of F))
    (W : ExposeV.FEt (pullback f k)) (hW : GoodActsTrivially f hg k L (tF ≫ j) W) :
    ∃ T : ExposeV.FEt (pullback f ρ),
      Nonempty ((ExposeV.FEt.pullback
          (fibreMap f (Spec.map (CommRingCat.ofHom (algebraMap R F))) hj)).obj T ≅
        (ExposeV.FEt.pullback (fibreMap f j rfl)).obj W) := by
  classical
  -- notation
  let iR : Spec (.of F) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R F))
  let h := pullback.snd f k
  let hF := pullback.snd f (j ≫ k)
  let fR := pullback.snd f ρ
  let e := secOf hg k
  let eF := secOf hg (j ≫ k)
  let eR := secOf hg ρ
  have he : e ≫ h = 𝟙 _ := secOf_snd hg k
  have heF : eF ≫ hF = 𝟙 _ := secOf_snd hg (j ≫ k)
  let β := fibreMap f j (rfl : j ≫ k = j ≫ k)
  let γ := fibreMap f iR hj
  let t := tF ≫ j
  -- connectedness
  have : ConnectedSpace ↥(pullback f k) := ExposeIX.connectedSpace_of_submersive h
  have : ConnectedSpace ↥(pullback f (j ≫ k)) := ExposeIX.connectedSpace_of_submersive hF
  have : ConnectedSpace ↥(pullback f ρ) := ExposeIX.connectedSpace_of_submersive fR
  have : ConnectedSpace ↥(pullback hF tF) :=
    GeometricallyConnected.geometrically_connectedSpace (f := hF) tF _ _
      (IsPullback.of_hasPullback hF tF)
  have : ConnectedSpace ↥(pullback h t) :=
    GeometricallyConnected.geometrically_connectedSpace (f := h) t _ _
      (IsPullback.of_hasPullback h t)
  -- the geometric points
  let aΩ := basePt h e he t
  let a := aΩ ≫ pullback.fst h t
  let aΩF := basePt hF eF heF tF
  let aF := aΩF ≫ pullback.fst hF tF
  have haF : aF = tF ≫ eF := basePt_fst hF eF heF tF
  have ha : a = t ≫ e := basePt_fst h e he t
  have hβa : aF ≫ β = a := by
    rw [haF, ha, Category.assoc, secOf_fibreMap j rfl hg, ← Category.assoc]
  -- `X_{Ω}` from `X_F` and from `X_R`
  have sqβ : IsPullback β hF h j := isPullback_fibreMap f j rfl
  have sqγ : IsPullback γ hF fR iR := isPullback_fibreMap f iR hj
  have sqΩ := (IsPullback.of_hasPullback hF tF).paste_horiz sqβ
  have sqR := (IsPullback.of_hasPullback hF tF).paste_horiz sqγ
  let θΩ := sqΩ.isoPullback
  let θR := sqR.isoPullback
  have hθΩfst : θΩ.hom ≫ pullback.fst h t = pullback.fst hF tF ≫ β := sqΩ.isoPullback_hom_fst
  have hθΩsnd : θΩ.hom ≫ pullback.snd h t = pullback.snd hF tF := sqΩ.isoPullback_hom_snd
  have hθRfst : θR.hom ≫ pullback.fst fR (tF ≫ iR) = pullback.fst hF tF ≫ γ :=
    sqR.isoPullback_hom_fst
  have hθΩ : aΩF ≫ θΩ.hom = aΩ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hθΩfst, ← Category.assoc]
      exact hβa
    · rw [Category.assoc, hθΩsnd]
      exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  -- the groups
  obtain ⟨π, -, hπσ, hπk⟩ := exists_retraction h e he t
  obtain ⟨πs, -, hπsσ, hπsk⟩ := exists_retraction hF eF heF tF
  obtain ⟨-, -, hr⟩ := properHomotopyExactSequenceFull h Ω t Ω aΩ
  obtain ⟨-, -, hrF⟩ := properHomotopyExactSequenceFull hF Ω tF Ω aΩF
  have hu := injective_map_fst_of_field K h Ω t Ω aΩ
  let u := FundamentalGroup.map (pullback.fst h t) aΩ
  let uF := FundamentalGroup.map (pullback.fst hF tF) aΩF
  let ι : FundamentalGroup aF →* FundamentalGroup a :=
    (ExposeV.FEt.fiberCongr Ω hβa).conjAut.toMonoidHom.comp (FundamentalGroup.map β aF)
  let ρG := FundamentalGroup.map γ aF
  let vΩ : FundamentalGroup aΩF →* FundamentalGroup aΩ :=
    (ExposeV.FEt.fiberCongr Ω hθΩ).conjAut.toMonoidHom.comp (FundamentalGroup.map θΩ.hom aΩF)
  -- `ι ∘ u_F` is `u ∘ v_Ω` up to an inner automorphism
  obtain ⟨c₁, hc₁⟩ := FundamentalGroup.exists_map_comp_eq_conj (pullback.fst hF tF) β θΩ.hom
    (pullback.fst h t) hθΩfst.symm aΩF hβa (by rw [hθΩ])
  have hιu : ∀ z, ι (uF z) = c₁ * u (vΩ z) * c₁⁻¹ := by
    intro z
    have e₁ : u (vΩ z) = (ExposeV.FEt.fiberCongr Ω (congrArg (· ≫ pullback.fst h t) hθΩ)).conjAut
        (FundamentalGroup.map (pullback.fst h t) (aΩF ≫ θΩ.hom)
          (FundamentalGroup.map θΩ.hom aΩF z)) :=
      DFunLike.congr_fun (FundamentalGroup.map_comp_conjAut_fiberCongr (pullback.fst h t) hθΩ) _
    rw [e₁]
    exact hc₁ z
  have hθΩb : Function.Bijective (FundamentalGroup.map θΩ.hom aΩF) :=
    ExposeV.autMap_bijective _ _
  have hvΩs : Function.Surjective vΩ := by
    intro x
    obtain ⟨w, hw⟩ := hθΩb.2 ((ExposeV.FEt.fiberCongr Ω hθΩ).conjAut.symm x)
    refine ⟨w, ?_⟩
    change (ExposeV.FEt.fiberCongr Ω hθΩ).conjAut (FundamentalGroup.map θΩ.hom aΩF w) = x
    rw [hw, MulEquiv.apply_symm_apply]
  have hvΩc : Continuous vΩ :=
    (ExposeV.continuous_conjAut _).comp (FundamentalGroup.continuous_map _ _)
  -- (b) `ι(ker π_s) ⊇ ker π`
  have hιP : ∀ x ∈ π.ker, ∃ y ∈ πs.ker, ι y = x := by
    intro x hx
    have hx' : c₁⁻¹ * x * c₁⁻¹⁻¹ ∈ π.ker := (inferInstance : π.ker.Normal).conj_mem x hx c₁⁻¹
    rw [hπk, ← hr] at hx'
    obtain ⟨w, hw⟩ := hx'
    obtain ⟨z, rfl⟩ := hvΩs w
    refine ⟨uF z, ?_, ?_⟩
    · rw [hπsk, ← hrF]
      exact ⟨z, rfl⟩
    · rw [hιu]
      rw [hw]
      group
  -- (a) compatibility with the sections
  obtain ⟨c₂, hc₂⟩ := FundamentalGroup.exists_map_comp_eq_conj eF β j e (secOf_fibreMap j rfl hg)
    tF (by rw [← haF]; exact hβa) ha.symm
  have hισ : ∀ γ', ι (sectionHom hF eF heF tF γ') =
      c₂ * sectionHom h e he t (FundamentalGroup.map j tF γ') * c₂⁻¹ := by
    intro γ'
    have e₁ : ι (sectionHom hF eF heF tF γ') =
        (ExposeV.FEt.fiberCongr Ω (by rw [← haF]; exact hβa : (tF ≫ eF) ≫ β = a)).conjAut
          (FundamentalGroup.map β (tF ≫ eF) (FundamentalGroup.map eF tF γ')) := by
      change (ExposeV.FEt.fiberCongr Ω hβa).conjAut (FundamentalGroup.map β aF
        ((ExposeV.FEt.fiberCongr Ω (basePt_fst hF eF heF tF).symm).conjAut
          (FundamentalGroup.map eF tF γ'))) = _
      have := DFunLike.congr_fun (FundamentalGroup.map_comp_conjAut_fiberCongr β
        (basePt_fst hF eF heF tF).symm) (FundamentalGroup.map eF tF γ')
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
      rw [this, fiberCongr_conjAut_conjAut]
    rw [e₁, hc₂ γ']
    rfl
  -- (c) the section lies in the kernel of `π₁(X_F) → π₁(X_R)`
  have hP : ∀ τ : ExposeV.etaleFundamentalGroup Ω (tF ≫ iR), τ = 1 :=
    ExposeX.etaleFundamentalGroup_eq_one_of_isSepClosed_residueField R Ω (tF ≫ iR)
  have hzero := ExposeV.etaleFundamentalGroup.map_comp_map_eq_one Ω eF γ iR eR
    (secOf_fibreMap iR hj hg) tF hP
  have hJσ : ∀ γ', sectionHom hF eF heF tF γ' ∈ ρG.ker := by
    intro γ'
    rw [MonoidHom.mem_ker]
    have := DFunLike.congr_fun (FundamentalGroup.map_comp_conjAut_fiberCongr γ
      (basePt_fst hF eF heF tF).symm) (FundamentalGroup.map eF tF γ')
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
    change ρG ((ExposeV.FEt.fiberCongr Ω (basePt_fst hF eF heF tF).symm).conjAut
      (FundamentalGroup.map eF tF γ')) = 1
    have h0 : FundamentalGroup.map γ (tF ≫ eF) (FundamentalGroup.map eF tF γ') = 1 :=
      DFunLike.congr_fun hzero γ'
    rw [this, h0, map_one]
  -- (d) `ρ ∘ u_F` is `π₁(X_{R,Ω}) → π₁(X_R)` up to isomorphisms
  have h' : (aΩF ≫ θR.hom) ≫ pullback.fst fR (tF ≫ iR) = aF ≫ γ := by
    rw [Category.assoc, hθRfst, ← Category.assoc]
  obtain ⟨c₃, hc₃⟩ := FundamentalGroup.exists_map_comp_eq_conj (pullback.fst hF tF) γ θR.hom
    (pullback.fst fR (tF ≫ iR)) hθRfst.symm aΩF (rfl : (aΩF ≫ pullback.fst hF tF) ≫ γ = aF ≫ γ) h'
  have hρu : ∀ z, ρG (uF z) = c₃ * (ExposeV.FEt.fiberCongr Ω h').conjAut
      (FundamentalGroup.map (pullback.fst fR (tF ≫ iR)) (aΩF ≫ θR.hom)
        (FundamentalGroup.map θR.hom aΩF z)) * c₃⁻¹ := by
    intro z
    have := hc₃ z
    rwa [fiberCongr_rfl_conjAut] at this
  have hθRb : Function.Bijective (FundamentalGroup.map θR.hom aΩF) :=
    ExposeV.autMap_bijective _ _
  -- `π₁(X_F) → π₁(X_R)` is onto
  have hsurjR : Function.Surjective (FundamentalGroup.map (pullback.fst fR (tF ≫ iR))
      (aΩF ≫ θR.hom)) :=
    ExposeX.surjective_map_fst_of_isSepClosed_residueField R fR Ω (tF ≫ iR) Ω (aΩF ≫ θR.hom)
  have hρs : Function.Surjective ρG := by
    intro x
    obtain ⟨w, hw⟩ := hsurjR ((ExposeV.FEt.fiberCongr Ω h').conjAut.symm (c₃⁻¹ * x * c₃))
    obtain ⟨z, rfl⟩ := hθRb.2 w
    refine ⟨uF z, ?_⟩
    rw [hρu, hw, MulEquiv.apply_symm_apply]
    group
  -- the core of X.3.8 over `R`
  obtain ⟨φF, hφF⟩ : ∃ φF : CommRingCat.of F ⟶ CommRingCat.of Ω, tF = Spec.map φF :=
    ⟨Spec.preimage tF, (Spec.map_preimage tF).symm⟩
  let φ : R →+* Ω := φF.hom.comp (algebraMap R F)
  have hφ : Function.Injective φ :=
    φF.hom.injective.comp (IsFractionRing.injective R F)
  have htR : tF ≫ iR = Spec.map (CommRingCat.ofHom φ) := by
    rw [hφF, ← Spec.map_comp]
    rfl
  have hfac : ExposeX.FactorsPrimeTo (FundamentalGroup.map (pullback.fst fR (tF ≫ iR))
      (aΩF ≫ θR.hom)) (ringExpChar (ResidueField R)) := by
    have key : ∀ (s : Spec (.of Ω) ⟶ Spec (.of R)) (_ : s = Spec.map (CommRingCat.ofHom φ))
        (a' : Spec (.of Ω) ⟶ pullback fR s), ExposeX.FactorsPrimeTo
          (FundamentalGroup.map (pullback.fst fR s) a') (ringExpChar (ResidueField R)) := by
      rintro s rfl a'
      exact factorsPrimeTo_map_fst_of_injective R fR Ω φ hφ Ω a'
    exact key _ htR _
  have hfac' : ExposeX.FactorsPrimeTo ((FundamentalGroup.map (pullback.fst fR (tF ≫ iR))
      (aΩF ≫ θR.hom)).comp (FundamentalGroup.map θR.hom aΩF)) (ringExpChar (ResidueField R)) :=
    ExposeX.FactorsPrimeTo.comp_continuousMulEquiv hfac
      (FundamentalGroup.mapContinuousMulEquiv θR.hom aΩF) (ContinuousMulEquiv.refl _)
  have hcore : ∀ y ∈ ρG.ker, y ∈ πs.ker → ∀ M ∈ lIndexSubgroups L π.ker, ι y ∈ M := by
    intro y hyρ hyπ M hM
    rw [hπsk, ← hrF] at hyπ
    obtain ⟨z, rfl⟩ := hyπ
    have hz : (FundamentalGroup.map (pullback.fst fR (tF ≫ iR)) (aΩF ≫ θR.hom)).comp
        (FundamentalGroup.map θR.hom aΩF) z = 1 := by
      have h1 := hρu z
      rw [MonoidHom.mem_ker.mp hyρ] at h1
      have h2 : (ExposeV.FEt.fiberCongr Ω h').conjAut
          (FundamentalGroup.map (pullback.fst fR (tF ≫ iR)) (aΩF ≫ θR.hom)
            (FundamentalGroup.map θR.hom aΩF z)) = 1 := by
        have := congrArg (fun x ↦ c₃⁻¹ * x * c₃) h1
        simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at this
        simpa using this.symm
      exact (MulEquiv.map_eq_one_iff _).mp h2
    -- the conjugated subgroup `M'`
    let M' := M.comap (MulAut.conj c₁).toMonoidHom
    have hM' : M' ∈ lIndexSubgroups L π.ker := comap_conj_mem_lIndexSubgroups hM c₁
    obtain ⟨hM'K, hM'n, hM'o, hM'L⟩ := hM'
    -- `u` as a map onto `ker π`
    have hmem (w : FundamentalGroup aΩ) : u w ∈ π.ker := by
      rw [hπk, ← hr]
      exact ⟨w, rfl⟩
    let u' : FundamentalGroup aΩ →* π.ker := u.codRestrict π.ker hmem
    have hu's : Function.Surjective u' := by
      rintro ⟨x, hx⟩
      rw [hπk, ← hr] at hx
      obtain ⟨w, rfl⟩ := hx
      exact ⟨w, rfl⟩
    have hu'c : Continuous u' := (FundamentalGroup.continuous_map _ _).subtype_mk _
    let N := ((M'.subgroupOf π.ker).comap u').comap vΩ
    have hNn : N.Normal := (hM'n.comap u').comap vΩ
    have hNo : IsOpen (N : Set (FundamentalGroup aΩF)) := (hM'o.preimage hu'c).preimage hvΩc
    have hNi : N.index = (M'.subgroupOf π.ker).index := by
      rw [Subgroup.index_comap_of_surjective _ hvΩs, Subgroup.index_comap_of_surjective _ hu's]
    have hcop : N.index.Coprime (ringExpChar (ResidueField R)) := by
      rw [hNi]
      exact Nat.coprime_of_dvd fun ℓ hℓ hdvd hdvdq ↦ hL ℓ (hM'L.2 ℓ hℓ hdvd) hdvdq
    have hzN : z ∈ N := FactorsPrimeTo.ker_le hfac' hNo hcop hz
    have hzM' : u (vΩ z) ∈ M' := hzN
    change ι (uF z) ∈ M
    rw [hιu]
    simpa [M', MulAut.conj_apply] using hzM'
  -- the good elements
  have hgood : ∀ y ∈ ρG.ker, IsGoodFor π.ker (sectionHom h e he t)
      (lIndexSubgroups L π.ker) (ι y) := fun y hy ↦
    isGoodFor_of_mem_ker_of_conj hπσ
      (fun M hM q hq m hm ↦ conj_mem_of_mem_lIndexSubgroups hM hq hm)
      (fun M hM g ↦ comap_conj_mem_lIndexSubgroups hM g) hπsσ ι (FundamentalGroup.map j tF) c₂
      hισ hιP ρG.ker hJσ hcore hy
  have hD : autHom (ExposeV.FEt.pullback β) (fiberPullbackIso β aF ≪≫
      ExposeV.FEt.fiberCongr Ω hβa) = ι := by
    rw [autHom_trans]
    rfl
  have hW' : ∀ σ : FundamentalGroup a, IsGoodFor π.ker (sectionHom h e he t)
      (lIndexSubgroups L π.ker) σ → ∀ w : (ExposeV.FEt.fiber Ω a).obj W, σ • w = w := by
    rw [hπk]
    exact hW
  obtain ⟨T, hT⟩ := exists_iso_of_forall_isGoodFor (π := π) (σ := sectionHom h e he t)
    (ExposeV.FEt.pullback β) (fiberPullbackIso β aF ≪≫ ExposeV.FEt.fiberCongr Ω hβa)
    (ExposeV.FEt.pullback γ) (fiberPullbackIso γ aF) hρs (fun y hy ↦ hD ▸ hgood y hy) W hW'
  exact ⟨T, hT⟩

end CodimOne

end SGA.SGA1.ExposeXIII
