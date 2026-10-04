/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Etale.GabberProper
import SGA.Foundations.Etale.GabberFiniteCover
import SGA.Foundations.Etale.GabberDescent

/-!
# Gabber's theorem: sections over a proper scheme over a noetherian henselian local ring

Let `q : Z ⟶ Spec A` be proper, `A` a noetherian henselian local ring, `i : Z₀ ⟶ Z` the closed
fibre and `F` an étale sheaf of sets on `Z`. Then `Γ(Z, F) ⟶ Γ(Z₀, i^* F)` is bijective
(`AlgebraicGeometry.properHenselianSectionsStatement`, Stacks 0A3S; Gabber's theorem, Stacks 09ZF,
in the proper case). Injectivity holds over any local ring
(`AlgebraicGeometry.injective_etaleSectionsRestrict_of_universallyClosed`); surjectivity is
`AlgebraicGeometry.surjective_etaleSectionsRestrict_of_henselianLocalRing`. Gabber's proof:

* a section `τ₀` over `Z₀` is, near every point of `Z₀`, the restriction of a section `a` of `F`
  over an affine étale neighbourhood `W` with agreement on the whole closed fibre of `W`
  (`exists_etaleAdjunction_unit_eq_of_isClosedImmersion`); finitely many `W` cover `Z`, and two of
  these local lifts agree over the closed fibre of `W ×_Z W'`;
* a finite surjective `π : Z' ⟶ Z` Zariski-locally factors through the `W`
  (Stacks 09Z0, `etaleFiniteRefinementStatement`), so the pulled back lifts are Zariski-local
  sections of `π^* F` on `Z'` which agree near the closed fibre of `Z'`; they glue to a global
  section `t` (Zariski `H⁰`, `exists_section_of_forall_closedFibre_of_henselianLocalRing`, as `Z'`
  is proper over `A`);
* `t` agrees with the pulled back lifts at the points over the closed fibre, so the locus of the
  points of `Z` near which `t` comes from a section of `F` is open (`π` is closed) and contains the
  closed fibre, hence is `Z`; `t` descends to `σ ∈ Γ(Z, F)`
  (`exists_etaleAdjunction_unit_eq_of_surjective`),
  and `σ` restricts to `τ₀` since both agree with the local lifts over the closed fibre.

Agreement of sections is tracked through agreement loci (`Scheme.etaleAgreementLocus`): their
compatibility with restriction (`mem_etaleAgreementLocus_map`) and with inverse images
(`mem_etaleAgreementLocus_etaleAdjunction_unit` and its converse), and sections of inverse images
given by morphisms `B ⟶ A` over the base (`Scheme.Etale.liftPullback`, which generalizes
`Scheme.Etale.sectionOfHom` from the terminal object to any étale scheme).

## References

* [Stacks Project, Tag 0A3S](https://stacks.math.columbia.edu/tag/0A3S)
* [Stacks Project, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF)
* [SGA 4, Exposé XII, 5.5][sga4]
-/

universe u

open CategoryTheory Limits Opposite IsLocalRing

-- As in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace AlgebraicGeometry.Scheme

section AgreementLocus

variable {X : Scheme.{u}} {H : Sheaf X.smallEtaleTopology (Type u)}

/-- A point of `B` at which the restrictions along `φ : B ⟶ C` of two sections agree maps into
their agreement locus. -/
lemma apply_mem_etaleAgreementLocus_of_mem {B C : X.Etale} (φ : B ⟶ C) {c d : H.obj.obj (op C)}
    {p : B.left} (hp : p ∈ etaleAgreementLocus H (H.obj.map φ.op c) (H.obj.map φ.op d)) :
    φ.left p ∈ etaleAgreementLocus H c d := by
  obtain ⟨V, g, v, h, rfl⟩ := hp
  refine ⟨V, g ≫ φ, v, ?_, rfl⟩
  rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, h]

/-- The agreement locus of the restrictions of two sections along `φ : B ⟶ C` contains the
preimage of their agreement locus. -/
lemma mem_etaleAgreementLocus_map {B C : X.Etale} (φ : B ⟶ C) {c d : H.obj.obj (op C)}
    {p : B.left} (hp : φ.left p ∈ etaleAgreementLocus H c d) :
    p ∈ etaleAgreementLocus H (H.obj.map φ.op c) (H.obj.map φ.op d) := by
  obtain ⟨V, g, v, h, hv⟩ := hp
  obtain ⟨z, hz₁, hz₂⟩ := Pullback.exists_preimage_pullback (f := g.left) (g := φ.left) v p hv
  let T : X.Etale := Etale.mk (pullback.snd g.left φ.left ≫ B.hom)
  let a : T ⟶ B := MorphismProperty.Over.homMk (pullback.snd g.left φ.left) rfl trivial
  let b : T ⟶ V := MorphismProperty.Over.homMk (pullback.fst g.left φ.left) (by
    change pullback.fst g.left φ.left ≫ V.hom = pullback.snd g.left φ.left ≫ B.hom
    rw [← MorphismProperty.Over.w g, pullback.condition_assoc, MorphismProperty.Over.w φ])
    trivial
  have hab : a ≫ φ = b ≫ g := by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.condition.symm
  refine ⟨T, a, z, ?_, hz₂⟩
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, hab, op_comp,
    Functor.map_comp_apply, Functor.map_comp_apply, h]

variable {T : Scheme.{u}} (u : T ⟶ X) {F : Sheaf X.smallEtaleTopology (Type u)}

/-- The square `T ×_X V ⟶ T ×_X A` over `V ⟶ A` is cartesian. -/
lemma isPullback_etalePullback_map {V A : X.Etale} (g : V ⟶ A) :
    IsPullback ((Etale.pullback u).map g).left (pullback.fst V.hom u) (pullback.fst A.hom u)
      g.left := by
  refine IsPullback.of_right ?_ (Etale.pullback_map_left_fst u g)
    (IsPullback.of_hasPullback A.hom u).flip
  rw [Etale.pullback_map_left_snd, MorphismProperty.Over.w g]
  exact (IsPullback.of_hasPullback V.hom u).flip

/-- The agreement locus of the inverse images `u^* c`, `u^* d` contains the preimage of the
agreement locus of `c` and `d`. -/
lemma mem_etaleAgreementLocus_etaleAdjunction_unit {A : X.Etale} {c d : F.obj.obj (op A)}
    {y : ((Etale.pullback u).obj A).left}
    (hy : pullback.fst A.hom u y ∈ etaleAgreementLocus F c d) :
    y ∈ etaleAgreementLocus ((etalePullback u).obj F)
      (((etaleAdjunction u).unit.app F).hom.app (op A) c)
      (((etaleAdjunction u).unit.app F).hom.app (op A) d) := by
  obtain ⟨V, g, v, h, hv⟩ := hy
  obtain ⟨y', hy'₁, hy'₂⟩ := exists_preimage_of_isPullback (isPullback_etalePullback_map u g) y v
    hv.symm
  refine ⟨(Etale.pullback u).obj V, (Etale.pullback u).map g, y', ?_, hy'₁⟩
  let η := (etaleAdjunction u).unit.app F
  have n (e : F.obj.obj (op A)) : η.hom.app (op V) (F.obj.map g.op e) =
      ((etalePullback u).obj F).obj.map ((Etale.pullback u).map g).op (η.hom.app (op A) e) :=
    NatTrans.naturality_apply η.hom g.op e
  rw [← n, ← n, h]

/-- Conversely, the agreement locus of `c` and `d` contains the image of the agreement locus of
`u^* c` and `u^* d`. -/
lemma apply_mem_etaleAgreementLocus_of_etaleAdjunction_unit {A : X.Etale} {c d : F.obj.obj (op A)}
    {y : ((Etale.pullback u).obj A).left}
    (hy : y ∈ etaleAgreementLocus ((etalePullback u).obj F)
      (((etaleAdjunction u).unit.app F).hom.app (op A) c)
      (((etaleAdjunction u).unit.app F).hom.app (op A) d)) :
    pullback.fst A.hom u y ∈ etaleAgreementLocus F c d := by
  let η := (etaleAdjunction u).unit.app F
  let O : ((Etale.pullback u).obj A).left.Opens :=
    ⟨_, isOpen_etaleAgreementLocus (F := (etalePullback u).obj F) (η.hom.app (op A) c)
      (η.hom.app (op A) d)⟩
  let B : T.Etale := Etale.mk (O.ι ≫ ((Etale.pullback u).obj A).hom)
  let k : B ⟶ (Etale.pullback u).obj A := MorphismProperty.Over.homMk O.ι rfl trivial
  have hk := map_eq_of_range_subset_etaleAgreementLocus k (by
    rintro _ ⟨z, rfl⟩
    exact z.2)
  exact range_subset_etaleAgreementLocus u k hk ⟨⟨y, hy⟩, rfl⟩

lemma etaleAgreementLocus_comm {W : X.Etale} (c d : H.obj.obj (op W)) :
    etaleAgreementLocus H c d = etaleAgreementLocus H d c := by
  ext x
  constructor <;> rintro ⟨V, g, v, h, hv⟩ <;> exact ⟨V, g, v, h.symm, hv⟩

end AgreementLocus

section LiftPullback

variable {T X : Scheme.{u}} (u : T ⟶ X)

/-- The morphism `B ⟶ T ×_X A` of étale `T`-schemes given by a morphism `b : B ⟶ A` over `X`. -/
def Etale.liftPullback (B : T.Etale) (A : X.Etale) (b : B.left ⟶ A.left)
    (hb : b ≫ A.hom = B.hom ≫ u) : B ⟶ (Etale.pullback u).obj A :=
  MorphismProperty.Over.homMk (pullback.lift b B.hom hb) (pullback.lift_snd _ _ _) trivial

@[reassoc (attr := simp)]
lemma Etale.liftPullback_left_fst (B : T.Etale) (A : X.Etale) (b : B.left ⟶ A.left)
    (hb : b ≫ A.hom = B.hom ≫ u) :
    (Etale.liftPullback u B A b hb).left ≫ pullback.fst A.hom u = b :=
  pullback.lift_fst _ _ _

lemma Etale.eq_liftPullback {B : T.Etale} {A : X.Etale} (φ : B ⟶ (Etale.pullback u).obj A) :
    φ = Etale.liftPullback u B A (φ.left ≫ pullback.fst A.hom u) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (· ≫ u) (MorphismProperty.Over.w φ)) := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp [Etale.liftPullback]
  · change φ.left ≫ pullback.snd A.hom u = pullback.lift _ _ _ ≫ pullback.snd A.hom u
    rw [pullback.lift_snd]
    exact MorphismProperty.Over.w φ

lemma Etale.comp_liftPullback {B B' : T.Etale} (φ : B' ⟶ B) (A : X.Etale) (b : B.left ⟶ A.left)
    (hb : b ≫ A.hom = B.hom ≫ u) :
    φ ≫ Etale.liftPullback u B A b hb = Etale.liftPullback u B' A (φ.left ≫ b) (by
      rw [Category.assoc, hb, ← Category.assoc, MorphismProperty.Over.w φ]) := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · change (φ.left ≫ pullback.lift b B.hom hb) ≫ pullback.fst A.hom u =
      pullback.lift _ _ _ ≫ pullback.fst A.hom u
    rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
  · change (φ.left ≫ pullback.lift b B.hom hb) ≫ pullback.snd A.hom u =
      pullback.lift _ _ _ ≫ pullback.snd A.hom u
    rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
    exact MorphismProperty.Over.w φ

lemma Etale.liftPullback_comp_pullback_map (B : T.Etale) {A A' : X.Etale} (c : A ⟶ A')
    (b : B.left ⟶ A.left) (hb : b ≫ A.hom = B.hom ≫ u) :
    Etale.liftPullback u B A b hb ≫ (Etale.pullback u).map c =
      Etale.liftPullback u B A' (b ≫ c.left)
        (by rw [Category.assoc, MorphismProperty.Over.w c, hb]) := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · rw [MorphismProperty.Comma.comp_left, Category.assoc, Etale.pullback_map_left_fst]
    simp [Etale.liftPullback]
  · rw [MorphismProperty.Comma.comp_left, Category.assoc, Etale.pullback_map_left_snd]
    simp [Etale.liftPullback]

variable {u} in
/-- Two sections of `u^* F` over `B`, given by morphisms `b₁ : B ⟶ A₁`, `b₂ : B ⟶ A₂` over `X`
and sections `c₁ ∈ F(A₁)`, `c₂ ∈ F(A₂)`, agree at every point `x` of `B` whose image under a
common factorization `m : B ⟶ P` (`P` with maps `pr₁ : P ⟶ A₁`, `pr₂ : P ⟶ A₂`) lies in the
agreement locus of the restrictions of `c₁` and `c₂` to `P`. -/
lemma mem_etaleAgreementLocus_liftPullback {F : Sheaf X.smallEtaleTopology (Type u)}
    (B : T.Etale) {A₁ A₂ P : X.Etale} (pr₁ : P ⟶ A₁) (pr₂ : P ⟶ A₂) (m : B.left ⟶ P.left)
    (hm : m ≫ P.hom = B.hom ≫ u) (b₁ : B.left ⟶ A₁.left) (b₂ : B.left ⟶ A₂.left)
    (hm₁ : m ≫ pr₁.left = b₁) (hm₂ : m ≫ pr₂.left = b₂) (hb₁ : b₁ ≫ A₁.hom = B.hom ≫ u)
    (hb₂ : b₂ ≫ A₂.hom = B.hom ≫ u) (c₁ : F.obj.obj (op A₁)) (c₂ : F.obj.obj (op A₂)) {x : B.left}
    (hx : m x ∈ etaleAgreementLocus F (F.obj.map pr₁.op c₁) (F.obj.map pr₂.op c₂)) :
    x ∈ etaleAgreementLocus ((etalePullback u).obj F)
      (((etalePullback u).obj F).obj.map (Etale.liftPullback u B A₁ b₁ hb₁).op
        (((etaleAdjunction u).unit.app F).hom.app (op A₁) c₁))
      (((etalePullback u).obj F).obj.map (Etale.liftPullback u B A₂ b₂ hb₂).op
        (((etaleAdjunction u).unit.app F).hom.app (op A₂) c₂)) := by
  subst hm₁ hm₂
  let G := (etalePullback u).obj F
  let η := (etaleAdjunction u).unit.app F
  let χ := Etale.liftPullback u B P m hm
  have e (A : X.Etale) (pr : P ⟶ A) (c : F.obj.obj (op A))
      (hb : (m ≫ pr.left) ≫ A.hom = B.hom ≫ u) :
      G.obj.map (Etale.liftPullback u B A (m ≫ pr.left) hb).op (η.hom.app (op A) c) =
        G.obj.map χ.op (η.hom.app (op P) (F.obj.map pr.op c)) := by
    have n : η.hom.app (op P) (F.obj.map pr.op c) =
        G.obj.map ((Etale.pullback u).map pr).op (η.hom.app (op A) c) :=
      NatTrans.naturality_apply η.hom pr.op c
    rw [n, ← Functor.map_comp_apply, ← op_comp, Etale.liftPullback_comp_pullback_map]
  rw [e, e]
  refine mem_etaleAgreementLocus_map χ ?_
  refine mem_etaleAgreementLocus_etaleAdjunction_unit u ?_
  change (χ.left ≫ pullback.fst P.hom u) x ∈ _
  rw [Etale.liftPullback_left_fst]
  exact hx

end LiftPullback

/-- A morphism to the terminal étale `X`-scheme is the structure morphism. -/
lemma Etale.hom_top_left {X : Scheme.{u}} {V : X.Etale} (g : V ⟶ Etale.top X) : g.left = V.hom :=
  (Category.comp_id g.left).symm.trans (MorphismProperty.Over.w g)

/-- The base change of the terminal étale scheme is terminal. -/
def Etale.isTerminalPullbackTop {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsTerminal ((Etale.pullback f).obj (Etale.top Y)) :=
  (Etale.isTerminalTop X).ofIso (Etale.pullbackTopIso f).symm

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

open Scheme Scheme.Etale

/-- **Gabber's theorem over a noetherian henselian local ring, surjectivity** (Stacks 0A3S, the
proof of 09ZF): for `q : Z ⟶ Spec A` proper, `A` a noetherian henselian local ring, `i : Z₀ ⟶ Z`
the closed fibre and `F` an étale sheaf of sets on `Z`, every section of `i^* F` over `Z₀` is the
restriction of a global section of `F`. -/
theorem surjective_etaleSectionsRestrict_of_henselianLocalRing {A : CommRingCat.{u}}
    [HenselianLocalRing A] [IsNoetherianRing A] {Z Z₀ : Scheme.{u}} (q : Z ⟶ Spec A) [IsProper q]
    {i : Z₀ ⟶ Z} {q₀ : Z₀ ⟶ Spec (.of (ResidueField A))}
    (hi : IsPullback i q₀ q (Spec.map (CommRingCat.ofHom (residue A))))
    (F : Sheaf Z.smallEtaleTopology (Type u)) :
    Function.Surjective (etaleSectionsRestrict i F) := by
  classical
  intro τ₀
  have : IsClosedImmersion i :=
    MorphismProperty.of_isPullback hi.flip
      (IsClosedImmersion.spec_of_surjective _ residue_surjective)
  have hrange : Set.range i = q ⁻¹' {closedPoint A} :=
    range_eq_preimage_closedPoint_of_isPullback hi
  have hcl (z : Z) (hz : q z = closedPoint A) : z ∈ Set.range i := hrange ▸ hz
  let G := (etalePullback i).obj F
  let η := (etaleAdjunction i).unit.app F
  -- Step 1: local lifts `a z₀ ∈ F(W z₀)` of `τ₀` around the points of the closed fibre
  choose W a w hwz hW ha using fun z₀ : Z₀ ↦
    exists_etaleAdjunction_unit_eq_of_isClosedImmersion i F τ₀ z₀
  let R : Z₀ → Set Z := fun z₀ ↦ Set.range (W z₀).hom
  have hRo (z₀ : Z₀) : IsOpen (R z₀) := (W z₀).hom.isOpenMap.isOpen_range
  have hcov (z : Z) : ∃ z₀, z ∈ R z₀ := by
    by_contra! h
    have hC : IsClosed (⋃ z₀, R z₀)ᶜ := (isOpen_iUnion hRo).isClosed_compl
    have := eq_empty_of_isClosed_of_forall_ne_closedPoint q hC fun z hz hzm ↦ by
      obtain ⟨z₀, rfl⟩ := hcl z hzm
      refine hz (Set.mem_iUnion.2 ⟨z₀, pullback.fst (W z₀).hom i (w z₀), ?_⟩)
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
      exact congrArg i (hwz z₀)
    exact (Set.eq_empty_iff_forall_notMem.1 this) z (by simpa using h)
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace q
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover R hRo
    (fun z _ ↦ Set.mem_iUnion.2 (hcov z))
  -- the local lifts agree over the closed fibre
  let W₂ (s s' : Z₀) : Z.Etale := Scheme.Etale.mk (pullback.fst (W s).hom (W s').hom ≫ (W s).hom)
  let pr₁ (s s' : Z₀) : W₂ s s' ⟶ W s :=
    MorphismProperty.Over.homMk (pullback.fst (W s).hom (W s').hom) rfl trivial
  let pr₂ (s s' : Z₀) : W₂ s s' ⟶ W s' :=
    MorphismProperty.Over.homMk (pullback.snd (W s).hom (W s').hom) pullback.condition.symm trivial
  have hagree (s s' : Z₀) (x : (W₂ s s').left) (hx : (W₂ s s').hom x ∈ Set.range i) :
      x ∈ etaleAgreementLocus F (F.obj.map (pr₁ s s').op (a s))
        (F.obj.map (pr₂ s s').op (a s')) := by
    have e (t : Z₀) (pr : W₂ s s' ⟶ W t) : η.hom.app (op (W₂ s s')) (F.obj.map pr.op (a t)) =
        G.obj.map ((Etale.isTerminalTop Z₀).from ((Etale.pullback i).obj (W₂ s s'))).op τ₀ := by
      have n : η.hom.app (op (W₂ s s')) (F.obj.map pr.op (a t)) =
          G.obj.map ((Etale.pullback i).map pr).op (η.hom.app (op (W t)) (a t)) :=
        NatTrans.naturality_apply η.hom pr.op (a t)
      rw [n, ha t, ← Functor.map_comp_apply, ← op_comp,
        (Etale.isTerminalTop Z₀).hom_ext (_ ≫ (Etale.isTerminalTop Z₀).from _)
          ((Etale.isTerminalTop Z₀).from _)]
    have e₁ := e s (pr₁ s s')
    have e₂ := e s' (pr₂ s s')
    have hk := range_subset_etaleAgreementLocus (F := F) (s := F.obj.map (pr₁ s s').op (a s))
      (t := F.obj.map (pr₂ s s').op (a s')) i (𝟙 ((Etale.pullback i).obj (W₂ s s')))
      (by rw [e₁, e₂])
    obtain ⟨z₀, hz₀⟩ := hx
    obtain ⟨y, hy, -⟩ := Pullback.exists_preimage_pullback (f := (W₂ s s').hom) (g := i) x z₀
      hz₀.symm
    exact hk ⟨y, hy⟩
  -- Step 2: a finite surjective `π : Z' ⟶ Z` which Zariski-locally factors through the `W s`
  have : IsNoetherian Z :=
    have := LocallyOfFiniteType.isLocallyNoetherian q
    { }
  have : ∀ s : S, IsAffine (W s.1).left := fun s ↦ hW s.1
  obtain ⟨Z', π, hπ, hπs, hloc⟩ := etaleFiniteRefinementStatement Z S (fun s ↦ W s.1) fun z ↦ by
    obtain ⟨s, hs, hz⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ z))
    obtain ⟨u, hu⟩ := hz
    exact ⟨⟨s, hs⟩, u, hu⟩
  choose O j g hO hg using hloc
  have : CompactSpace Z' := QuasiCompact.compactSpace_of_compactSpace π
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun z' ↦ (O z' : Set Z'))
    (fun z' ↦ (O z').2) (fun z' _ ↦ Set.mem_iUnion.2 ⟨z', hO z'⟩)
  have hTcov (z' : Z') : ∃ α ∈ T, z' ∈ O α := by
    obtain ⟨α, hα, hz⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ z'))
    exact ⟨α, hα, hz⟩
  -- Step 3: on `Z'`, the pulled back local lifts glue (Zariski `H⁰`, chart form)
  let G' := (etalePullback π).obj F
  let η' := (etaleAdjunction π).unit.app F
  have hπcl (z' : Z') (hz' : (π ≫ q) z' = closedPoint A) : π z' ∈ Set.range i := hcl _ hz'
  let ψ (α : Z') : ofOpens (O α) ⟶ (Etale.pullback π).obj (W (j α).1) :=
    Etale.liftPullback π (ofOpens (O α)) (W (j α).1) (g α) (hg α)
  let sec (α : Z') : G'.obj.obj (op (ofOpens (O α))) :=
    G'.obj.map (ψ α).op (η'.hom.app (op (W (j α).1)) (a (j α).1))
  have hsec (α : Z') {B : Z'.Etale} (φ : B ⟶ ofOpens (O α)) :
      G'.obj.map φ.op (sec α) = G'.obj.map (Etale.liftPullback π B (W (j α).1) (φ.left ≫ g α)
        (by rw [Category.assoc, hg α, ← Category.assoc]
            exact congrArg (· ≫ π) (MorphismProperty.Over.w φ))).op
        (η'.hom.app (op (W (j α).1)) (a (j α).1)) := by
    simp only [sec, ψ]
    rw [← Functor.map_comp_apply, ← op_comp, Etale.comp_liftPullback]
  -- two sections given by lifts through `W s` and `W s'` agree over the closed fibre
  have hagree' {B : Z'.Etale} (s s' : Z₀) (b : B.left ⟶ (W s).left) (b' : B.left ⟶ (W s').left)
      (hb : b ≫ (W s).hom = B.hom ≫ π) (hb' : b' ≫ (W s').hom = B.hom ≫ π) (x : B.left)
      (hx : (π ≫ q) (B.hom x) = closedPoint A) :
      x ∈ etaleAgreementLocus G'
        (G'.obj.map (Etale.liftPullback π B (W s) b hb).op (η'.hom.app (op (W s)) (a s)))
        (G'.obj.map (Etale.liftPullback π B (W s') b' hb').op (η'.hom.app (op (W s')) (a s'))) := by
    refine mem_etaleAgreementLocus_liftPullback B (pr₁ s s') (pr₂ s s') (pullback.lift b b'
      (by rw [hb, hb'])) (by
        change pullback.lift b b' _ ≫ pullback.fst _ _ ≫ (W s).hom = _
        rw [pullback.lift_fst_assoc, hb]) b b' (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      hb hb' (a s) (a s') (hagree s s' _ ?_)
    change (pullback.lift b b' _ ≫ pullback.fst _ _ ≫ (W s).hom) x ∈ _
    rw [pullback.lift_fst_assoc, hb]
    exact hπcl _ hx
  have hres {U U' V : Z'.Opens} (h₁ : U' ≤ U) (h₂ : U ≤ V) (σ : G'.obj.obj (op (ofOpens V))) :
      G'.obj.map (ofOpensHom h₁).op (G'.obj.map (ofOpensHom h₂).op σ) =
        G'.obj.map (ofOpensHom (h₁.trans h₂)).op σ := by
    rw [← Functor.map_comp_apply, ← op_comp, ofOpensHom_comp]
  have h₀ (α β : T) (z' : Z') (hz' : (π ≫ q) z' = closedPoint A) (hα : z' ∈ O α)
      (hβ : z' ∈ O β) : ∃ (U : Z'.Opens) (hUα : U ≤ O α) (hUβ : U ≤ O β), z' ∈ U ∧
        G'.obj.map (ofOpensHom hUα).op (sec α) = G'.obj.map (ofOpensHom hUβ).op (sec β) := by
    let V := O α ⊓ O β
    let σ₁ := G'.obj.map (ofOpensHom (inf_le_left : V ≤ O α)).op (sec α)
    let σ₂ := G'.obj.map (ofOpensHom (inf_le_right : V ≤ O β)).op (sec β)
    let L := etaleAgreementLocus G' σ₁ σ₂
    have hLo : IsOpen L := isOpen_etaleAgreementLocus σ₁ σ₂
    let v : (ofOpens V).left := ⟨z', hα, hβ⟩
    have hvL : v ∈ L := by
      change v ∈ etaleAgreementLocus G'
        (G'.obj.map (ofOpensHom (inf_le_left : V ≤ O α)).op (sec α))
        (G'.obj.map (ofOpensHom (inf_le_right : V ≤ O β)).op (sec β))
      rw [hsec, hsec]
      exact hagree' _ _ _ _ _ _ v hz'
    let U : Z'.Opens := ⟨V.ι '' L, V.ι.isOpenEmbedding.isOpenMap L hLo⟩
    have hUV : U ≤ V := by
      rintro _ ⟨x, -, rfl⟩
      exact (Scheme.Opens.range_ι V).le ⟨x, rfl⟩
    refine ⟨U, hUV.trans inf_le_left, hUV.trans inf_le_right, ⟨v, hvL, rfl⟩, ?_⟩
    rw [← hres hUV inf_le_left, ← hres hUV inf_le_right]
    refine map_eq_of_range_subset_etaleAgreementLocus (ofOpensHom hUV) ?_
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hyL, hy⟩ := x.2
    have : (ofOpensHom hUV).left x = y := by
      apply V.ι.isOpenEmbedding.injective
      have e := congrArg (fun φ ↦ φ x) (Z'.homOfLE_ι hUV)
      simp only [Scheme.Hom.comp_apply] at e
      exact e.trans hy.symm
    rw [this]
    exact hyL
  obtain ⟨t, ht⟩ := exists_section_of_forall_closedFibre_of_henselianLocalRing (π ≫ q) G'
    (fun α : T ↦ O α) (fun α ↦ sec α) (fun z' _ ↦ by
      obtain ⟨α, hα, hz⟩ := hTcov z'
      exact ⟨⟨α, hα⟩, hz⟩) h₀
  -- Step 4: over the closed fibre, `t` is the image of the local lifts
  have hkey (s : Z₀) (p : ((Etale.pullback π).obj (W s)).left)
      (hp : (π ≫ q) (pullback.snd (W s).hom π p) = closedPoint A) :
      p ∈ etaleAgreementLocus G' (η'.hom.app (op (W s)) (a s))
        (G'.obj.map ((Etale.isTerminalTop Z').from ((Etale.pullback π).obj (W s))).op t) := by
    let P := (Etale.pullback π).obj (W s)
    obtain ⟨α, hαT, hzα⟩ := hTcov (pullback.snd (W s).hom π p)
    obtain ⟨U, hUα, hzU, htU⟩ := ht ⟨α, hαT⟩ _ hp hzα
    dsimp only at hUα htU
    let PU : P.left.Opens := (pullback.snd (W s).hom π) ⁻¹ᵁ U
    let B : Z'.Etale := Scheme.Etale.mk (PU.ι ≫ P.hom)
    let jU : B ⟶ P := MorphismProperty.Over.homMk PU.ι rfl trivial
    have hBU : Set.range B.hom ⊆ (U : Set Z') := by
      rintro _ ⟨x, rfl⟩
      exact x.2
    let kU : B ⟶ ofOpens U := liftOfOpens hBU
    let p' : B.left := ⟨p, hzU⟩
    have h₁ := hagree' (B := B) s (j α).1 (jU.left ≫ pullback.fst (W s).hom π)
      ((kU ≫ ofOpensHom hUα).left ≫ g α) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        exact congrArg (· ≫ π) (MorphismProperty.Over.w jU)) (by
        rw [Category.assoc, hg α, ← Category.assoc]
        exact congrArg (· ≫ π) (MorphismProperty.Over.w (kU ≫ ofOpensHom hUα))) p' hp
    rw [← Etale.eq_liftPullback π jU, ← hsec α (kU ≫ ofOpensHom hUα), op_comp,
      Functor.map_comp_apply, ← htU, ← Functor.map_comp_apply, ← op_comp,
      (Etale.isTerminalTop Z').hom_ext (kU ≫ (Etale.isTerminalTop Z').from (ofOpens U))
        (jU ≫ (Etale.isTerminalTop Z').from P), op_comp, Functor.map_comp_apply] at h₁
    exact apply_mem_etaleAgreementLocus_of_mem jU h₁
  -- Step 5: `t` descends to `Z`: near every point it is the image of a section of `F`
  let sZ : G'.obj.obj (op ((Etale.pullback π).obj (Etale.top Z))) :=
    G'.obj.map (Etale.pullbackTopIso π).hom.op t
  have hsZ {V : Z.Etale} (g₀ : V ⟶ Etale.top Z) :
      G'.obj.map ((Etale.pullback π).map g₀).op sZ =
        G'.obj.map ((Etale.isTerminalTop Z').from ((Etale.pullback π).obj V)).op t := by
    rw [← Functor.map_comp_apply, ← op_comp,
      (Etale.isTerminalTop Z').hom_ext (_ ≫ (Etale.pullbackTopIso π).hom)
        ((Etale.isTerminalTop Z').from _)]
  let Good : Set Z := {z | ∃ (V : Z.Etale) (g₀ : V ⟶ Etale.top Z) (v : V.left)
    (f : F.obj.obj (op V)), g₀.left v = z ∧
      η'.hom.app (op V) f = G'.obj.map ((Etale.pullback π).map g₀).op sZ}
  have hGo : IsOpen Good := by
    refine isOpen_iff_forall_mem_open.2 fun z ⟨V, g₀, v, f, hv, hf⟩ ↦
      ⟨Set.range g₀.left, ?_, g₀.left.isOpenMap.isOpen_range, ⟨v, hv⟩⟩
    rintro _ ⟨v', rfl⟩
    exact ⟨V, g₀, v', f, rfl, hf⟩
  have hG₀ (z : Z) (hz : q z = closedPoint A) : z ∈ Good := by
    obtain ⟨s, w₀, rfl⟩ := hcov z
    let P := (Etale.pullback π).obj (W s)
    let L := etaleAgreementLocus G' (η'.hom.app (op (W s)) (a s))
      (G'.obj.map ((Etale.isTerminalTop Z').from P).op t)
    have hK : IsClosed (pullback.fst (W s).hom π '' Lᶜ) :=
      (pullback.fst (W s).hom π).isClosedMap _ (isOpen_etaleAgreementLocus _ _).isClosed_compl
    have hw₀ : w₀ ∉ pullback.fst (W s).hom π '' Lᶜ := by
      rintro ⟨p, hpL, hp⟩
      refine hpL (hkey s p ?_)
      change (pullback.snd (W s).hom π ≫ π ≫ q) p = _
      rw [← Category.assoc, ← pullback.condition, Category.assoc, Scheme.Hom.comp_apply, hp]
      exact hz
    let W' : (W s).left.Opens := ⟨_, hK.isOpen_compl⟩
    let V : Z.Etale := Scheme.Etale.mk (W'.ι ≫ (W s).hom)
    let ιV : V ⟶ W s := MorphismProperty.Over.homMk W'.ι rfl trivial
    refine ⟨V, (Etale.isTerminalTop Z).from V, ⟨w₀, hw₀⟩, F.obj.map ιV.op (a s), ?_, ?_⟩
    · rw [Etale.hom_top_left]
      rfl
    · have n : η'.hom.app (op V) (F.obj.map ιV.op (a s)) =
          G'.obj.map ((Etale.pullback π).map ιV).op (η'.hom.app (op (W s)) (a s)) :=
        NatTrans.naturality_apply η'.hom ιV.op (a s)
      rw [n, hsZ, (Etale.isTerminalTop Z').hom_ext ((Etale.isTerminalTop Z').from _)
        ((Etale.pullback π).map ιV ≫ (Etale.isTerminalTop Z').from P), op_comp,
        Functor.map_comp_apply]
      refine map_eq_of_range_subset_etaleAgreementLocus _ ?_
      rintro _ ⟨y, rfl⟩
      by_contra hy
      have e : pullback.fst (W s).hom π (((Etale.pullback π).map ιV).left y) =
          W'.ι (pullback.fst V.hom π y) := by
        change (((Etale.pullback π).map ιV).left ≫ pullback.fst (W s).hom π) y = _
        rw [Etale.pullback_map_left_fst]
        rfl
      have hmem : W'.ι (pullback.fst V.hom π y) ∈ (W' : Set (W s).left) :=
        (Scheme.Opens.range_ι W').le ⟨_, rfl⟩
      exact hmem ⟨_, hy, e⟩
  have hgood (z : Z) : z ∈ Good := by
    have := eq_empty_of_isClosed_of_forall_ne_closedPoint q hGo.isClosed_compl
      fun z hz hzm ↦ hz (hG₀ z hzm)
    by_contra h
    exact (Set.eq_empty_iff_forall_notMem.1 this) z h
  obtain ⟨σ, hσ⟩ := Scheme.exists_etaleAdjunction_unit_eq_of_surjective π F sZ hgood
  refine ⟨σ, ?_⟩
  -- Step 6: the restriction of `σ` to the closed fibre is `τ₀`
  have hσW (s : Z₀) (x : (W s).left) (hx : q ((W s).hom x) = closedPoint A) :
      x ∈ etaleAgreementLocus F (F.obj.map ((Etale.isTerminalTop Z).from (W s)).op σ) (a s) := by
    obtain ⟨z', hz'⟩ := π.surjective ((W s).hom x)
    obtain ⟨p, hp₁, hp₂⟩ := Pullback.exists_preimage_pullback (f := (W s).hom) (g := π) x z'
      hz'.symm
    have h₁ := hkey s p (by
      change q (π (pullback.snd (W s).hom π p)) = _
      rw [hp₂, hz']
      exact hx)
    have e : G'.obj.map ((Etale.isTerminalTop Z').from ((Etale.pullback π).obj (W s))).op t =
        η'.hom.app (op (W s)) (F.obj.map ((Etale.isTerminalTop Z).from (W s)).op σ) := by
      have n : η'.hom.app (op (W s)) (F.obj.map ((Etale.isTerminalTop Z).from (W s)).op σ) =
          G'.obj.map ((Etale.pullback π).map ((Etale.isTerminalTop Z).from (W s))).op
            (η'.hom.app (op (Etale.top Z)) σ) :=
        NatTrans.naturality_apply η'.hom _ σ
      rw [n, hσ, hsZ]
    rw [e, etaleAgreementLocus_comm] at h₁
    have h₂ := apply_mem_etaleAgreementLocus_of_etaleAdjunction_unit π h₁
    rwa [hp₁] at h₂
  have hall (z₀ : Z₀) : z₀ ∈ etaleAgreementLocus G (etaleSectionsRestrict i F σ) τ₀ := by
    let P₀ := (Etale.pullback i).obj (W z₀)
    let fr := (Etale.isTerminalTop Z₀).from P₀
    have e₁ : G.obj.map fr.op (etaleSectionsRestrict i F σ) =
        η.hom.app (op (W z₀)) (F.obj.map ((Etale.isTerminalTop Z).from (W z₀)).op σ) := by
      have n : η.hom.app (op (W z₀)) (F.obj.map ((Etale.isTerminalTop Z).from (W z₀)).op σ) =
          G.obj.map ((Etale.pullback i).map ((Etale.isTerminalTop Z).from (W z₀))).op
            (η.hom.app (op (Etale.top Z)) σ) :=
        NatTrans.naturality_apply η.hom _ σ
      rw [n, etaleSectionsRestrict, sectionAlong, ← Functor.map_comp_apply, ← op_comp,
        (Etale.isTerminalPullbackTop i).hom_ext (fr ≫ _) ((Etale.pullback i).map _)]
    have hw : w z₀ ∈ etaleAgreementLocus G (G.obj.map fr.op (etaleSectionsRestrict i F σ))
        (G.obj.map fr.op τ₀) := by
      rw [e₁, ← ha z₀]
      refine mem_etaleAgreementLocus_etaleAdjunction_unit i (hσW z₀ _ ?_)
      have e : (pullback.fst (W z₀).hom i ≫ (W z₀).hom ≫ q) (w z₀) = closedPoint A := by
        rw [← Category.assoc, pullback.condition, Category.assoc, Scheme.Hom.comp_apply]
        have h₁ : pullback.snd (W z₀).hom i (w z₀) = z₀ := hwz z₀
        rw [h₁]
        exact hrange.le ⟨z₀, rfl⟩
      exact e
    have h := apply_mem_etaleAgreementLocus_of_mem fr hw
    have h₃ : P₀.hom (w z₀) = z₀ := hwz z₀
    rw [Etale.hom_top_left] at h
    exact h₃ ▸ h
  have := map_eq_of_range_subset_etaleAgreementLocus (𝟙 (Etale.top Z₀))
    (s := etaleSectionsRestrict i F σ) (t := τ₀) (fun x _ ↦ hall x)
  simpa using this

/-- **Stacks 0A3S, noetherian case** (Gabber's theorem for proper schemes over a noetherian
henselian local ring), for any cartesian square defining the closed fibre `i : Z₀ ⟶ Z`: the
restriction `Γ(Z, F) ⟶ Γ(Z₀, i^* F)` is bijective. -/
theorem bijective_etaleSectionsRestrict_of_henselianLocalRing {A : CommRingCat.{u}}
    [HenselianLocalRing A] [IsNoetherianRing A] {Z Z₀ : Scheme.{u}} (q : Z ⟶ Spec A) [IsProper q]
    {i : Z₀ ⟶ Z} {q₀ : Z₀ ⟶ Spec (.of (ResidueField A))}
    (hi : IsPullback i q₀ q (Spec.map (CommRingCat.ofHom (residue A))))
    (F : Sheaf Z.smallEtaleTopology (Type u)) :
    Function.Bijective (etaleSectionsRestrict i F) :=
  ⟨injective_etaleSectionsRestrict_of_universallyClosed q hi F,
    surjective_etaleSectionsRestrict_of_henselianLocalRing q hi F⟩

/-- **Stacks 0A3S, noetherian case**: `ProperHenselianSectionsStatement` holds. -/
theorem properHenselianSectionsStatement : ProperHenselianSectionsStatement.{u} :=
  fun _ _ _ _ q _ F ↦ bijective_etaleSectionsRestrict_of_henselianLocalRing q
    (IsPullback.of_hasPullback _ _) F

end AlgebraicGeometry
