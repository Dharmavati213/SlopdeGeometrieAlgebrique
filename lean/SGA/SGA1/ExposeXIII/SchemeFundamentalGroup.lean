/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import SGA.SGA1.ExposeXIII.AffineLinePrimeToP
import SGA.SGA1.ExposeXIII.ArtinSchreier
import SGA.SGA1.ExposeXIII.HomotopySequence
import SGA.SGA1.ExposeXIII.ProLQuotient
import SGA.SGA1.ExposeV.FundamentalGroupFunctoriality

/-!
# SGA 1, Exposé XIII, §4: fundamental groups of schemes and the sequences of XIII.4.0

We use the fundamental group of a scheme of Exposé V: `FEt X` is the category of finite étale
coverings of `X` (`SGA.SGA1.ExposeV.FEt`), and `FundamentalGroup x` is `π₁(X, x) = Aut F_x` for the
fibre functor `F_x` at a geometric point `x : Spec Ω ⟶ X`
(`SGA.SGA1.ExposeV.etaleFundamentalGroup`), a profinite group. Its underlying functor to sets is
`fiberFunctor x : E ↦ Hom_X(x, E)` (`fiberFunctorIso`). A morphism `g : Y ⟶ X` induces the
continuous homomorphism `π₁(Y, y) →* π₁(X, y ≫ g)` of V.7 (`FundamentalGroup.map`, which is
`autHom` of the base change functor), so the criteria of `SGA.SGA1.ExposeXIII.HomotopySequence`
apply. The composite `π₁(X_s̄) → π₁(X) → π₁(S)` is trivial
(`FundamentalGroup.map_comp_map_fst_eq_one`, XIII.4.0). We record:

* `IsProLExact` / `IsProLShortExact`: exactness of `π₁^L(X_s̄) → π'₁(X) → π₁(S) → 1`
  (resp. with `1 →` on the left), expressed through `π₁(X_s̄) → π₁(X) → π₁(S)`; see
  `isProLExact_iff` for the equivalence with the sequence of XIII.4.0;
* the semidirect product decompositions of XIII.4.5 from such sequences
  (`exists_semidirectProduct_of_isProLShortExact`, `exists_semidirectProduct_range_of_isProLExact`);
* the Künneth formula XIII.4.6 in characteristic zero (statement only; the proper case is proved
  in `SGA.SGA1.ExposeXIII.ProperHomotopySequence`);
* Remark XIII.2.13: the Artin–Schreier description of `Hom(π₁(𝔸¹), ℤ/p)` (proved as
  `affineLineArtinSchreier` in `SGA.SGA1.ExposeXIII.AffineLineFundamentalGroup`) and Abhyankar's
  conjecture for the affine line (statement), with the consequences SGA draws from them. That
  `π₁(𝔸¹_k)` is not topologically finitely generated is proved unconditionally in
  `SGA.SGA1.ExposeXIII.AffineLineFundamentalGroup`; the case `g = 0`, `n = 1` of XIII.2.12,
  `π₁^{p'}(𝔸¹_k) = 1` (`affineLinePrimeToPTrivialStatement`), and hence the necessary condition
  `G^{(p')} = 1` in Abhyankar's conjecture (`sylowSup_eq_top_of_affineLine`), are proved.

XIII.4.4 (the homotopy exact sequence for proper separable morphisms) is proved in
`SGA.SGA1.ExposeXIII.ProperHomotopySequence`. The general form of XIII.4.1–4.3 needs local
acyclicity and cohomological properness (SGA 4 XV, XIII §1); only its formal part is proved (in
`HomotopySequence` and `ProLQuotient`).
-/

universe u w

namespace SGA.SGA1.ExposeXIII

open AlgebraicGeometry CategoryTheory Limits MorphismProperty

section AutTopology

variable {C : Type*} [Category C] {C' : Type*} [Category C'] (F : C ⥤ Type w)

/-- The embedding of `Aut F` into the product of the permutation groups of the fibres. -/
def autToPerm : Aut F →* ∀ X, Equiv.Perm (F.obj X) where
  toFun σ X := (σ.app X).toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The topology of pointwise convergence on the fibres of a `Type`-valued functor (the profinite
topology of V.5 when the fibres are finite). -/
@[instance_reducible]
def autTopology : TopologicalSpace (Aut F) :=
  TopologicalSpace.induced (autToPerm F) (@Pi.topologicalSpace _ _ fun _ ↦ ⊥)

lemma isTopologicalGroup_autTopology :
    @IsTopologicalGroup (Aut F) (autTopology F) _ := by
  let : ∀ X, TopologicalSpace (Equiv.Perm (F.obj X)) := fun _ ↦ ⊥
  have : ∀ X, DiscreteTopology (Equiv.Perm (F.obj X)) := fun _ ↦ ⟨rfl⟩
  exact topologicalGroup_induced (autToPerm F)

variable {F} {F' : C' ⥤ Type w} (H : C ⥤ C') (v : H ⋙ F' ≅ F)

/-- The homomorphisms of automorphism groups induced by functors compatible with fibre functors
are continuous. -/
lemma continuous_autHom_autTopology :
    @Continuous _ _ (autTopology F') (autTopology F) (autHom H v) := by
  let : ∀ X, TopologicalSpace (Equiv.Perm (F.obj X)) := fun _ ↦ ⊥
  let : ∀ X, TopologicalSpace (Equiv.Perm (F'.obj X)) := fun _ ↦ ⊥
  have : ∀ X, DiscreteTopology (Equiv.Perm (F'.obj X)) := fun _ ↦ ⟨rfl⟩
  let := autTopology F
  let := autTopology F'
  apply continuous_induced_rng.2
  refine continuous_pi fun X ↦ ?_
  have : (fun σ ↦ (autToPerm F ∘ autHom H v) σ X) =
      (fun τ : Equiv.Perm (F'.obj (H.obj X)) ↦
          ((v.app X).toEquiv.symm.trans τ).trans (v.app X).toEquiv) ∘
        (fun σ : Aut F' ↦ autToPerm F' σ (H.obj X)) := by
    funext σ
    rfl
  rw [this]
  exact continuous_of_discreteTopology.comp ((continuous_apply _).comp continuous_induced_dom)

end AutTopology

section Fet

noncomputable section

/-- Finite étale morphisms of schemes (`SGA.SGA1.ExposeV.finiteEtaleHom`). -/
abbrev finiteEtale : MorphismProperty Scheme.{u} := ExposeV.finiteEtaleHom

/-- V.7: the category of finite étale coverings of `X` (`SGA.SGA1.ExposeV.FEt`). -/
abbrev FEt (X : Scheme.{u}) : Type (u + 1) := ExposeV.FEt X

variable {X Y : Scheme.{u}} {Ω : Type u} [Field Ω]

/-- V.4–V.5, V.7: the functor `E ↦ Hom_X(x, E)` of geometric points over a geometric point
`x : Spec Ω ⟶ X`; it is the fibre functor `ExposeV.FEt.fiber Ω x` followed by the inclusion of
finite sets into sets (`fiberFunctorIso`). -/
def fiberFunctor (x : Spec (.of Ω) ⟶ X) : FEt X ⥤ Type u where
  obj E := {s : Spec (.of Ω) ⟶ E.left // s ≫ E.hom = x}
  map φ := ↾fun s ↦ ⟨s.1 ≫ φ.left, by rw [Category.assoc, Over.w φ, s.2]⟩

@[simp]
lemma fiberFunctor_map_coe (x : Spec (.of Ω) ⟶ X) {E E' : FEt X} (φ : E ⟶ E')
    (s : (fiberFunctor x).obj E) : ((fiberFunctor x).map φ s).1 = s.1 ≫ φ.left :=
  rfl

/-- The fibre functor of V.7 at `x`, viewed in sets, is the functor of geometric points. -/
def fiberFunctorIso (x : Spec (.of Ω) ⟶ X) :
    ExposeV.FEt.fiber Ω x ⋙ FintypeCat.incl ≅ fiberFunctor x :=
  ExposeV.FEt.fiberInclIso Ω x ≪≫ NatIso.ofComponents (fun _ ↦ Equiv.toIso
    { toFun := fun a ↦ ⟨a.left, Over.w a⟩
      invFun := fun s ↦ Over.homMk s.1 s.2
      left_inv := fun _ ↦ Over.OverMorphism.ext rfl
      right_inv := fun _ ↦ rfl })
    (fun _ ↦ rfl)

/-- V.5, V.7: the fundamental group `π₁(X, x)`, the automorphism group of the fibre functor at the
geometric point `x`, with its profinite topology (`SGA.SGA1.ExposeV.etaleFundamentalGroup`). -/
abbrev FundamentalGroup (x : Spec (.of Ω) ⟶ X) : Type (u + 1) :=
  ExposeV.etaleFundamentalGroup Ω x

variable (x : Spec (.of Ω) ⟶ X)

/-- Base change identifies `Hom_Y(y, g^*E)` with `Hom_X(g ∘ y, E)`. -/
def fiberPullbackEquiv (g : Y ⟶ X) (y : Spec (.of Ω) ⟶ Y) (E : FEt X) :
    {s : Spec (.of Ω) ⟶ pullback E.hom g // s ≫ pullback.snd E.hom g = y} ≃
      {t : Spec (.of Ω) ⟶ E.left // t ≫ E.hom = y ≫ g} where
  toFun s := ⟨s.1 ≫ pullback.fst E.hom g, by
    rw [Category.assoc, pullback.condition, ← Category.assoc, s.2]⟩
  invFun t := ⟨pullback.lift t.1 y t.2, pullback.lift_snd _ _ _⟩
  left_inv s := Subtype.ext (pullback.hom_ext (pullback.lift_fst _ _ _)
    ((pullback.lift_snd _ _ _).trans s.2.symm))
  right_inv t := Subtype.ext (pullback.lift_fst _ _ _)

omit [Field Ω] in
lemma pullback_lift_aux (g : Y ⟶ X) {A A' W : Scheme.{u}} (e : A ⟶ X) (e' : A' ⟶ X)
    (φ : A ⟶ A') (t : W ⟶ pullback e g)
    (w : (pullback.fst e g ≫ φ) ≫ e' = pullback.snd e g ≫ g) :
    (t ≫ pullback.lift (pullback.fst e g ≫ φ) (pullback.snd e g) w) ≫
      pullback.fst e' g = (t ≫ pullback.fst e g) ≫ φ := by
  rw [Category.assoc, pullback.lift_fst, Category.assoc]

/-- V.7: base change identifies the fibre functor of `g^*E` at `y` with that of `E` at `g ∘ y`
(`SGA.SGA1.ExposeV.FEt.pullbackFiberIso`). -/
def fiberPullbackIso (g : Y ⟶ X) (y : Spec (.of Ω) ⟶ Y) :
    ExposeV.FEt.pullback g ⋙ ExposeV.FEt.fiber Ω y ≅ ExposeV.FEt.fiber Ω (y ≫ g) :=
  ExposeV.FEt.pullbackFiberIso Ω g y

/-- V.6, V.7: the continuous homomorphism `π₁(Y, y) → π₁(X, g ∘ y)` induced by `g : Y ⟶ X`
(`SGA.SGA1.ExposeV.etaleFundamentalGroup.map`). -/
def FundamentalGroup.map (g : Y ⟶ X) (y : Spec (.of Ω) ⟶ Y) :
    FundamentalGroup y →* FundamentalGroup (y ≫ g) :=
  ExposeV.etaleFundamentalGroup.map Ω g y

/-- `FundamentalGroup.map` is the homomorphism `autHom` of V.6 attached to the base change
functor, so the criteria of `SGA.SGA1.ExposeXIII.HomotopySequence` apply to it. -/
lemma FundamentalGroup.map_eq_autHom (g : Y ⟶ X) (y : Spec (.of Ω) ⟶ Y) :
    FundamentalGroup.map g y = autHom (ExposeV.FEt.pullback g) (fiberPullbackIso g y) :=
  rfl

lemma FundamentalGroup.continuous_map (g : Y ⟶ X) (y : Spec (.of Ω) ⟶ Y) :
    Continuous (FundamentalGroup.map g y) :=
  ExposeV.etaleFundamentalGroup.continuous_map Ω g y

/-- XIII.4.0, X.1.4: for `f : X ⟶ S` and a geometric point `s̄` of `S`, the composite
`π₁(X_s̄, a) → π₁(X, a) → π₁(S, a)` is trivial, since `X_s̄ → S` factors through `Spec Ω`
whose fundamental group is trivial. -/
theorem FundamentalGroup.map_comp_map_fst_eq_one {S : Scheme.{u}} (f : X ⟶ S) [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (Ω' : Type u) [Field Ω'] [IsSepClosed Ω']
    (a : Spec (.of Ω') ⟶ pullback f s) :
    (FundamentalGroup.map f (a ≫ pullback.fst f s)).comp
      (FundamentalGroup.map (pullback.fst f s) a) = 1 :=
  ExposeV.etaleFundamentalGroup.map_comp_map_eq_one Ω' (pullback.fst f s) f (pullback.snd f s) s
    pullback.condition a (ExposeV.etaleFundamentalGroup.eq_one_of_isSepClosed Ω' Ω _)

/-- Changing the geometric point along an equality `x = x'` (`SGA.SGA1.ExposeV.FEt.fiberCongr`)
commutes with the maps of fundamental groups. -/
lemma FundamentalGroup.map_comp_conjAut_fiberCongr {S : Scheme.{u}} (f : X ⟶ S)
    {x x' : Spec (.of Ω) ⟶ X} (e : x = x') :
    (FundamentalGroup.map f x').comp (ExposeV.FEt.fiberCongr Ω e).conjAut.toMonoidHom =
      (ExposeV.FEt.fiberCongr Ω (congrArg (· ≫ f) e)).conjAut.toMonoidHom.comp
        (FundamentalGroup.map f x) := by
  subst e
  ext σ : 1
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ExposeV.FEt.fiberCongr, eqToIso_refl,
    Iso.conjAut_apply, Iso.refl_symm, Iso.refl_trans]
  exact (congrArg _ (Iso.trans_refl σ)).trans (Iso.trans_refl _).symm

end

end Fet

section Exactness

variable (L : Set ℕ) {G'' G' G : Type*} [Group G''] [Group G'] [Group G]
  [TopologicalSpace G''] [TopologicalSpace G'] [IsTopologicalGroup G']

/-- The sequence `π₁^L(X_s̄) → π'₁(X) → π₁(S) → 1` of XIII.4.0 is exact, expressed through
`h' : π₁(X_s̄) → π₁(X)` and `h : π₁(X) → π₁(S)` (see `isProLExact_iff`). -/
def IsProLExact (h' : G'' →* G') (h : G' →* G) : Prop :=
  h.comp h' = 1 ∧ Function.Surjective h ∧ h.ker ≤ h'.range ⊔ primeKernel L h

/-- The sequence `1 → π₁^L(X_s̄) → π'₁(X) → π₁(S) → 1` of XIII.4.3 is exact. -/
def IsProLShortExact (h' : G'' →* G') (h : G' →* G) : Prop :=
  IsProLExact L h' h ∧ (primeKernel L h).comap h' ≤ proLKernel L G''

variable {L} (h' : G'' →* G') (h : G' →* G) (hh' : Continuous h') (hcomp : h.comp h' = 1)

/-- `IsProLExact` is the exactness of `u : π₁^L(X_s̄) → π'₁(X)`, `v : π'₁(X) → π₁(S)` and
`π₁(S) → 1`. -/
theorem isProLExact_iff :
    IsProLExact L h' h ↔
      Function.Surjective (primeQuotientLift L h) ∧
        (proLToPrimeQuotient L h' h hh' hcomp).range = (primeQuotientLift L h).ker := by
  rw [exact_primeQuotient_iff L h' h hh' hcomp, IsProLExact]
  exact ⟨fun ⟨_, h₁, h₂⟩ ↦ ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ ↦ ⟨hcomp, h₁, h₂⟩⟩

/-- `IsProLShortExact` is the exactness of `1 → π₁^L(X_s̄) → π'₁(X) → π₁(S) → 1`. -/
theorem isProLShortExact_iff :
    IsProLShortExact L h' h ↔
      Function.Injective (proLToPrimeQuotient L h' h hh' hcomp) ∧
      Function.Surjective (primeQuotientLift L h) ∧
        (proLToPrimeQuotient L h' h hh' hcomp).range = (primeQuotientLift L h).ker := by
  rw [IsProLShortExact, isProLExact_iff h' h hh' hcomp,
    injective_proLToPrimeQuotient_iff L h' h hh' hcomp]
  exact and_comm

/-- XIII.4.5: if `1 → π₁^L(X_s̄) → π'₁(X) → π₁(S) → 1` is exact and `π₁(X) → π₁(S)` has a
section (induced by a section of `X → S`), then `π'₁(X)` is a semidirect product of `π₁(S)` by
`π₁^L(X_s̄)`. -/
theorem exists_semidirectProduct_of_isProLShortExact (hex : IsProLShortExact L h' h)
    (w : G →* G') (hw : h.comp w = MonoidHom.id G) :
    ∃ (φ : G →* MulAut (ProLQuotient L G''))
      (e : ProLQuotient L G'' ⋊[φ] G ≃* PrimeQuotient L h),
      (∀ a, e (SemidirectProduct.inl a) = proLToPrimeQuotient L h' h hh' hex.1.1 a) ∧
      ∀ c, e (SemidirectProduct.inr c) = QuotientGroup.mk (w c) := by
  obtain ⟨hinj, hsurj, hrange⟩ := (isProLShortExact_iff h' h hh' hex.1.1).mp hex
  obtain ⟨φ, e, he₁, he₂, -⟩ := exists_semidirectProduct_mulEquiv
    (proLToPrimeQuotient L h' h hh' hex.1.1) (primeQuotientLift L h) hinj hsurj hrange
    ((QuotientGroup.mk' _).comp w) (by
      ext c
      exact DFunLike.congr_fun hw c)
  exact ⟨φ, e, he₁, he₂⟩

/-- XIII.4.5, without the injectivity of `u` (which is XIII.4.3): if
`π₁^L(X_s̄) → π'₁(X) → π₁(S) → 1` is exact and `w : π₁(S) → π₁(X)` is such that
`π₁(S) → π₁(X) → π₁(S)` is bijective (as for the map induced by a section, up to the change of
base point), then `π'₁(X)` is a semidirect product of `π₁(S)` by the image of `π₁^L(X_s̄)`. -/
theorem exists_semidirectProduct_range_of_isProLExact (hex : IsProLExact L h' h) (w : G →* G')
    (hw : Function.Bijective (h.comp w)) :
    ∃ (φ : G →* MulAut (proLToPrimeQuotient L h' h hh' hex.1).range)
      (e : (proLToPrimeQuotient L h' h hh' hex.1).range ⋊[φ] G ≃* PrimeQuotient L h),
      (∀ a, e (SemidirectProduct.inl a) = a) ∧
      ∀ c, primeQuotientLift L h (e (SemidirectProduct.inr c)) = c := by
  obtain ⟨hsurj, hrange⟩ := (isProLExact_iff h' h hh' hex.1).mp hex
  let ψ : G ≃* G := MulEquiv.ofBijective (h.comp w) hw
  let s : G →* PrimeQuotient L h := ((QuotientGroup.mk' _).comp w).comp ψ.symm.toMonoidHom
  have hs : (primeQuotientLift L h).comp s = MonoidHom.id G := by
    ext c
    exact ψ.apply_symm_apply c
  obtain ⟨φ, e, he₁, he₂, -⟩ := exists_semidirectProduct_mulEquiv
    (proLToPrimeQuotient L h' h hh' hex.1).range.subtype (primeQuotientLift L h)
    Subtype.val_injective hsurj (by rw [Subgroup.range_subtype, hrange]) s hs
  refine ⟨φ, e, he₁, fun c ↦ ?_⟩
  rw [he₂]
  exact DFunLike.congr_fun hs c

end Exactness

section Statements

/-- The set of primes different from all residue characteristics of `S`. -/
def primesInvertibleOn (S : Scheme.{u}) : Set ℕ :=
  {ℓ | ℓ.Prime ∧ ∀ s : S, ringChar (S.residueField s) ≠ ℓ}

/-- XIII.4.6 (Künneth formula) in characteristic zero (statement only): for connected schemes
`X`, `Y` over a separably closed field `k` of characteristic `0`, `X` quasi-compact and
quasi-separated, the projections induce an isomorphism
`π₁(X ×_k Y, c) ≅ π₁(X, a) × π₁(Y, b)`. In characteristic zero the desingularization
hypotheses a), b) of XIII.4.6 hold (Hironaka) and `p'` is the set of all primes, so
`π₁^{p'} = π₁`; in characteristic `p > 0` the statement needs these hypotheses, which are not
formalized. For `X` proper the formula holds in every characteristic
(`bijective_proLMap_prod_of_isProper`, from X.1.7). -/
def KunnethCharZeroStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsSepClosed k] [CharZero k] {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k)) [QuasiCompact fX] [QuasiSeparated fX]
    [ConnectedSpace X] [ConnectedSpace Y] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (c : Spec (.of Ω) ⟶ pullback fX fY),
    Function.Bijective ((FundamentalGroup.map (pullback.fst fX fY) c).prod
      (FundamentalGroup.map (pullback.snd fX fY) c))

end Statements

section AffineLine

/-- `ℤ/pℤ` (written multiplicatively) as a discrete topological group, in any universe. -/
def DiscreteZMod (p : ℕ) : Type u := ULift.{u} (Multiplicative (ZMod p))

instance (p : ℕ) : Group (DiscreteZMod.{u} p) :=
  inferInstanceAs (Group (ULift (Multiplicative (ZMod p))))

instance (p : ℕ) : TopologicalSpace (DiscreteZMod.{u} p) := ⊥

instance (p : ℕ) : DiscreteTopology (DiscreteZMod.{u} p) := ⟨rfl⟩

instance (p : ℕ) [NeZero p] : Finite (DiscreteZMod.{u} p) :=
  inferInstanceAs (Finite (ULift (Multiplicative (ZMod p))))

/-- The identification `DiscreteZMod p ≃* Multiplicative (ZMod p)`. -/
def DiscreteZMod.equiv (p : ℕ) : DiscreteZMod.{u} p ≃* Multiplicative (ZMod p) :=
  MulEquiv.ulift

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A topological group is topologically finitely generated if a finite subset generates a
dense subgroup. -/
def IsTopologicallyFG (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ s : Finset G, Dense (Subgroup.closure (s : Set G) : Set G)

omit [IsTopologicalGroup G] in
/-- A topologically finitely generated group has only finitely many continuous homomorphisms to
a finite discrete group. -/
theorem finite_continuousMonoidHom_of_isTopologicallyFG (hG : IsTopologicallyFG G)
    (Q : Type*) [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q] :
    Finite (ContinuousMonoidHom G Q) := by
  obtain ⟨s, hs⟩ := hG
  have hinj : Function.Injective fun φ : ContinuousMonoidHom G Q ↦ fun x : s ↦ φ x := by
    intro φ ψ hφψ
    have hle : Subgroup.closure (s : Set G) ≤ (φ.toMonoidHom.eqLocus ψ.toMonoidHom) := by
      rw [Subgroup.closure_le]
      intro x hx
      exact congrFun hφψ ⟨x, hx⟩
    have hclosed : IsClosed ((φ.toMonoidHom.eqLocus ψ.toMonoidHom : Subgroup G) : Set G) :=
      isClosed_eq φ.continuous ψ.continuous
    have htop : ((φ.toMonoidHom.eqLocus ψ.toMonoidHom : Subgroup G) : Set G) = Set.univ :=
      Set.eq_univ_of_univ_subset (hs.closure_eq ▸ hclosed.closure_subset_iff.mpr hle)
    ext x
    have : x ∈ ((φ.toMonoidHom.eqLocus ψ.toMonoidHom : Subgroup G) : Set G) := htop ▸ trivial
    exact this
  exact Finite.of_injective _ hinj

/-- The Artin–Schreier description of the `ℤ/p`-coverings of the affine line (XI.6.9, as used in
XIII.2.13): for `k` algebraically closed of characteristic `p`, the continuous homomorphisms
`π₁(𝔸¹_k, x) → ℤ/p` correspond bijectively to `k[T]/℘(k[T])`. Proved as
`SGA.SGA1.ExposeXIII.affineLineArtinSchreier` in `SGA.SGA1.ExposeXIII.AffineLineFundamentalGroup`,
from XI's `artinSchreierEquivContinuousMonoidHom`. -/
def AffineLineArtinSchreierStatement (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharP k p] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))),
    Nonempty (ContinuousMonoidHom (FundamentalGroup x) (DiscreteZMod.{u} p) ≃
      Polynomial k ⧸ (artinSchreierPoly k p).range)

/-- XIII.2.13, as SGA argues: granting the Artin–Schreier description of its `ℤ/p`-quotients,
the fundamental group of the affine line over an algebraically closed field of characteristic
`p > 0` is not topologically finitely generated. (Proved unconditionally, for any field of
characteristic `p`, as `not_isTopologicallyFG_fundamentalGroup_affineLine`.) -/
theorem not_isTopologicallyFG_affineLine (p : ℕ) [Fact p.Prime]
    (hAS : AffineLineArtinSchreierStatement.{u} p) (k : Type u) [Field k] [IsAlgClosed k]
    [CharP k p] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))) :
    ¬ IsTopologicallyFG (FundamentalGroup x) := by
  intro hfg
  obtain ⟨e⟩ := hAS k Ω x
  have : Finite (ContinuousMonoidHom (FundamentalGroup x) (DiscreteZMod.{u} p)) :=
    finite_continuousMonoidHom_of_isTopologicallyFG hfg _
  have hinf := infinite_quotient_artinSchreierPoly (k := k) (p := p)
  exact (Finite.of_equiv _ e).false

/-- The set `p'` of primes different from `p`. -/
def primesDifferentFrom (p : ℕ) : Set ℕ := {ℓ | ℓ.Prime ∧ ℓ ≠ p}

/-- The case `g = 0`, `n = 1` of XIII.2.12, used in XIII.2.13: over an algebraically closed
field of characteristic `p`, the maximal prime-to-`p` quotient `π₁^{p'}(𝔸¹)` of the fundamental
group of the affine line is trivial. Proved below (`affineLinePrimeToPTrivialStatement`) without
Riemann's existence theorem: a connected Galois covering of `𝔸¹` of degree prime to `p` is tamely
ramified at `∞` and has a rational point over `0`, so it is trivial by the lattice method of
XI.1.1 (`SGA.SGA1.ExposeXI.finrank_eq_one_of_le_card`, `SGA.SGA1.ExposeXI.finrank_eq_one_of_tame`;
see `SGA.SGA1.ExposeXIII.AffineLinePrimeToP`). -/
def AffineLinePrimeToPTrivialStatement (p : ℕ) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharP k p] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))),
    proLKernel (primesDifferentFrom p) (FundamentalGroup x) = ⊤

/-- XIII.2.12 for `g = 0`, `n = 1`: `π₁^{p'}(𝔸¹_k) = 1` for `k` algebraically closed of
characteristic `p` (`proLKernel_etaleFundamentalGroup_eq_top`). -/
theorem affineLinePrimeToPTrivialStatement (p : ℕ) : AffineLinePrimeToPTrivialStatement.{u} p :=
  fun k _ _ _ Ω _ _ x ↦ proLKernel_etaleFundamentalGroup_eq_top k Ω p x

/-- Abhyankar's conjecture for the affine line (proved by M. Raynaud), as recalled in
XIII.2.13 (statement only): a finite group is the Galois group of a connected étale covering of
`𝔸¹_k` (a continuous quotient of `π₁(𝔸¹_k)`) iff it is generated by its Sylow `p`-subgroups,
i.e. iff `G^{(p')} = 1`. -/
def AbhyankarAffineLineStatement (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharP k p] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))) (G : Type u) [Group G] [Finite G]
    [TopologicalSpace G] [DiscreteTopology G],
    (∃ φ : ContinuousMonoidHom (FundamentalGroup x) G, Function.Surjective φ) ↔ sylowSup p G = ⊤

/-- XIII.2.13, the necessary condition: if `π₁^{p'}(𝔸¹) = 1`, every finite quotient `G` of
`π₁(𝔸¹)` satisfies `G^{(p')} = 1`, i.e. is generated by its Sylow `p`-subgroups. More generally,
a finite continuous quotient of a topological group with trivial maximal prime-to-`p` quotient
is generated by its Sylow `p`-subgroups. -/
theorem sylowSup_eq_top_of_surjective {p : ℕ} [Fact p.Prime] {Γ : Type*} [Group Γ]
    [TopologicalSpace Γ] (hΓ : proLKernel (primesDifferentFrom p) Γ = ⊤) (G : Type*) [Group G]
    [Finite G] [TopologicalSpace G] [DiscreteTopology G] (φ : ContinuousMonoidHom Γ G)
    (hφ : Function.Surjective φ) : sylowSup p G = ⊤ := by
  let q : Γ →* PrimeToPQuotient p G := (QuotientGroup.mk' _).comp φ.toMonoidHom
  let : TopologicalSpace (PrimeToPQuotient p G) := ⊥
  have : DiscreteTopology (PrimeToPQuotient p G) := ⟨rfl⟩
  have hq : Continuous q :=
    (continuous_of_discreteTopology :
      Continuous (QuotientGroup.mk' (primeToPKernel p G) : G → PrimeToPQuotient p G)).comp
      φ.continuous
  have hL : IsLGroup (primesDifferentFrom p) (PrimeToPQuotient p G) := by
    have hcop : (primeToPKernel p G).index.Coprime p := by
      rw [primeToPKernel_eq_sylowSup]
      obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
      have hle : (P : Subgroup G) ≤ sylowSup p G :=
        le_iSup (fun P : Sylow p G ↦ (P : Subgroup G)) P
      exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr
        fun h ↦ P.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hle))))
    refine ⟨inferInstance, fun ℓ hℓ hdvd ↦ ⟨hℓ, ?_⟩⟩
    rintro rfl
    rw [← Subgroup.index_eq_card] at hdvd
    exact (Nat.Prime.coprime_iff_not_dvd hℓ).mp hcop.symm hdvd
  have hker : proLKernel (primesDifferentFrom p) Γ ≤ q.ker := proLKernel_le_ker hL q hq
  rw [hΓ, top_le_iff] at hker
  rw [← primeToPKernel_eq_sylowSup, eq_top_iff]
  intro g _
  obtain ⟨x, rfl⟩ := hφ g
  have : q x = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    trivial
  exact (QuotientGroup.eq_one_iff _).mp this

/-- XIII.2.13: the necessary condition in Abhyankar's conjecture for the affine line, deduced
from `π₁^{p'}(𝔸¹) = 1` (`affineLinePrimeToPTrivialStatement`): every finite quotient of
`π₁(𝔸¹_k)` is generated by its Sylow `p`-subgroups. -/
theorem sylowSup_eq_top_of_affineLine (p : ℕ) [Fact p.Prime] (k : Type u) [Field k]
    [IsAlgClosed k] [CharP k p] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))) (G : Type u) [Group G] [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] (φ : ContinuousMonoidHom (FundamentalGroup x) G)
    (hφ : Function.Surjective φ) : sylowSup p G = ⊤ :=
  sylowSup_eq_top_of_surjective (affineLinePrimeToPTrivialStatement.{u} p k Ω x) G φ hφ

end AffineLine

end SGA.SGA1.ExposeXIII
